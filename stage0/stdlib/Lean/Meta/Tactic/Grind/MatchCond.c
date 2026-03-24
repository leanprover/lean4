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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
lean_inc(v___y_200_);
lean_inc(v___y_199_);
v___x_211_ = lean_apply_12(v_k_198_, v_b_205_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, lean_box(0));
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v_b_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v_b_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec(v___y_213_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_226_, uint8_t v_bi_227_, lean_object* v_type_228_, lean_object* v_k_229_, uint8_t v_kind_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; 
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc(v___y_231_);
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
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec(v___y_257_);
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
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec(v___y_291_);
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
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec(v___y_316_);
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
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v___y_368_);
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
lean_dec(v_i_382_);
lean_dec_ref(v_lhss_u03b1s_381_);
v___x_400_ = lean_unsigned_to_nat(0u);
v_eAbst_401_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_383_, v_tys_384_, v_e_380_, v___x_400_);
lean_dec_ref(v_tys_384_);
lean_dec_ref(v_xs_383_);
v___x_402_ = 1;
v___x_403_ = 1;
v___x_404_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_385_, v_eAbst_401_, v___x_399_, v___x_402_, v___x_399_, v___x_402_, v___x_403_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec_ref(v_tysxs_385_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref(v___x_404_);
v___x_406_ = l_Lean_mkAppN(v_a_405_, v_args_386_);
v___x_407_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_406_, v_a_392_);
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
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec(v___y_509_);
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
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec(v_a_553_);
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
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec(v___y_589_);
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
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
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
lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_645_; 
v_fst_643_ = lean_ctor_get(v_x_641_, 0);
lean_inc(v_fst_643_);
v_snd_644_ = lean_ctor_get(v_x_641_, 1);
lean_inc(v_snd_644_);
lean_dec_ref(v_x_641_);
v___x_645_ = lean_apply_2(v_h__1_642_, v_fst_643_, v_snd_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_646_, lean_object* v_h__1_647_, lean_object* v_h__2_648_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_646_) == 1)
{
lean_object* v_val_649_; lean_object* v___x_650_; 
lean_dec(v_h__2_648_);
v_val_649_ = lean_ctor_get(v_00_u03b1_x3f_646_, 0);
lean_inc(v_val_649_);
lean_dec_ref(v_00_u03b1_x3f_646_);
v___x_650_ = lean_apply_1(v_h__1_647_, v_val_649_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; 
lean_dec(v_h__1_647_);
v___x_651_ = lean_apply_2(v_h__2_648_, v_00_u03b1_x3f_646_, lean_box(0));
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_652_, lean_object* v_00_u03b1_x3f_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_653_) == 1)
{
lean_object* v_val_656_; lean_object* v___x_657_; 
lean_dec(v_h__2_655_);
v_val_656_ = lean_ctor_get(v_00_u03b1_x3f_653_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v_00_u03b1_x3f_653_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
lean_inc_ref(v_matchCond_668_);
v___x_684_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_668_);
v___x_685_ = l_Lean_Expr_isApp(v___x_684_);
if (v___x_685_ == 0)
{
lean_dec_ref(v___x_684_);
goto v___jp_680_;
}
else
{
lean_object* v_arg_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_arg_686_ = lean_ctor_get(v___x_684_, 1);
lean_inc_ref(v_arg_686_);
v___x_687_ = l_Lean_Expr_appFnCleanup___redArg(v___x_684_);
v___x_688_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_689_ = l_Lean_Expr_isConstOf(v___x_687_, v___x_688_);
lean_dec_ref(v___x_687_);
if (v___x_689_ == 0)
{
lean_dec_ref(v_arg_686_);
goto v___jp_680_;
}
else
{
lean_object* v_lhss_u03b1s_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_matchCond_668_);
lean_inc_ref(v_arg_686_);
v_lhss_u03b1s_690_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_686_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_693_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_686_, v_lhss_u03b1s_690_, v___x_691_, v___x_692_, v___x_692_, v___x_692_, v___x_692_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v___x_693_;
}
}
v___jp_680_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_matchCond_668_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec(v_a_695_);
return v_res_706_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_710_; lean_object* v_dummy_711_; 
v___x_710_ = lean_box(0);
v_dummy_711_ = l_Lean_Expr_sort___override(v___x_710_);
return v_dummy_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_lhs_712_, lean_object* v_rhs_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_Expr_hasLooseBVars(v_lhs_712_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_712_, v_a_714_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_867_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_867_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_867_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_867_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v_ctor_731_; 
v_ctor_731_ = lean_ctor_get_uint8(v_a_727_, sizeof(void*)*11 + 2);
if (v_ctor_731_ == 0)
{
uint8_t v_interpreted_732_; 
v_interpreted_732_ = lean_ctor_get_uint8(v_a_727_, sizeof(void*)*11 + 1);
if (v_interpreted_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec(v_a_727_);
lean_dec_ref(v_rhs_713_);
v___x_733_ = lean_box(v_interpreted_732_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v_self_737_; uint8_t v___x_738_; 
v_self_737_ = lean_ctor_get(v_a_727_, 0);
lean_inc_ref(v_self_737_);
lean_dec(v_a_727_);
v___x_738_ = l_Lean_Expr_hasLooseBVars(v_rhs_713_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
lean_del_object(v___x_729_);
lean_inc_ref(v_rhs_713_);
v___x_739_ = l_Lean_Meta_isLitValue(v_rhs_713_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; uint8_t v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
v___x_741_ = lean_unbox(v_a_740_);
if (v___x_741_ == 0)
{
lean_dec(v_a_740_);
lean_dec_ref(v_self_737_);
lean_dec_ref(v_rhs_713_);
return v___x_739_;
}
else
{
lean_object* v___x_742_; 
lean_dec_ref(v___x_739_);
v___x_742_ = l_Lean_Meta_normLitValue(v_self_737_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref(v___x_742_);
v___x_744_ = l_Lean_Meta_normLitValue(v_rhs_713_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_757_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_757_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
uint8_t v___x_749_; 
v___x_749_ = lean_expr_eqv(v_a_743_, v_a_745_);
lean_dec(v_a_745_);
lean_dec(v_a_743_);
if (v___x_749_ == 0)
{
lean_object* v___x_751_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v_a_740_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_740_);
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
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_a_740_);
v___x_753_ = lean_box(v___x_738_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_753_);
v___x_755_ = v___x_747_;
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
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_743_);
lean_dec(v_a_740_);
v_a_758_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_744_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_744_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_740_);
lean_dec_ref(v_rhs_713_);
v_a_766_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_742_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_742_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
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
}
else
{
lean_dec_ref(v_self_737_);
lean_dec_ref(v_rhs_713_);
return v___x_739_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec_ref(v_self_737_);
lean_dec_ref(v_rhs_713_);
v___x_774_ = lean_box(v_ctor_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_774_);
v___x_776_ = v___x_729_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
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
else
{
lean_object* v_self_778_; lean_object* v___x_779_; 
lean_del_object(v___x_729_);
v_self_778_ = lean_ctor_get(v_a_727_, 0);
lean_inc_ref(v_self_778_);
lean_dec(v_a_727_);
lean_inc_ref(v_self_778_);
v___x_779_ = l_Lean_Meta_isConstructorApp_x3f(v_self_778_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_858_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_858_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_858_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_858_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
if (lean_obj_tag(v_a_780_) == 1)
{
lean_object* v_val_784_; lean_object* v___x_785_; 
lean_del_object(v___x_782_);
v_val_784_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_val_784_);
lean_dec_ref(v_a_780_);
lean_inc_ref(v_rhs_713_);
v___x_785_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_713_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_845_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_845_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_845_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_845_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
if (lean_obj_tag(v_a_786_) == 1)
{
lean_object* v_toConstantVal_790_; lean_object* v_val_791_; lean_object* v_toConstantVal_792_; lean_object* v_numParams_793_; lean_object* v_numFields_794_; lean_object* v_name_795_; lean_object* v_name_796_; uint8_t v___x_797_; 
v_toConstantVal_790_ = lean_ctor_get(v_val_784_, 0);
lean_inc_ref(v_toConstantVal_790_);
v_val_791_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_val_791_);
lean_dec_ref(v_a_786_);
v_toConstantVal_792_ = lean_ctor_get(v_val_791_, 0);
lean_inc_ref(v_toConstantVal_792_);
lean_dec(v_val_791_);
v_numParams_793_ = lean_ctor_get(v_val_784_, 3);
lean_inc(v_numParams_793_);
v_numFields_794_ = lean_ctor_get(v_val_784_, 4);
lean_inc(v_numFields_794_);
lean_dec(v_val_784_);
v_name_795_ = lean_ctor_get(v_toConstantVal_790_, 0);
lean_inc(v_name_795_);
lean_dec_ref(v_toConstantVal_790_);
v_name_796_ = lean_ctor_get(v_toConstantVal_792_, 0);
lean_inc(v_name_796_);
lean_dec_ref(v_toConstantVal_792_);
v___x_797_ = lean_name_eq(v_name_795_, v_name_796_);
lean_dec(v_name_796_);
lean_dec(v_name_795_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_numFields_794_);
lean_dec(v_numParams_793_);
lean_dec_ref(v_self_778_);
lean_dec_ref(v_rhs_713_);
v___x_798_ = lean_box(v_ctor_731_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_798_);
v___x_800_ = v___x_788_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
if (v___x_725_ == 0)
{
lean_object* v_nargs_802_; lean_object* v_nargs_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_dummy_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_788_);
v_nargs_802_ = l_Lean_Expr_getAppNumArgs(v_self_778_);
v_nargs_803_ = l_Lean_Expr_getAppNumArgs(v_rhs_713_);
v___x_804_ = lean_nat_add(v_numParams_793_, v_numFields_794_);
lean_dec(v_numFields_794_);
v___x_805_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_802_);
v___x_807_ = lean_mk_array(v_nargs_802_, v_dummy_806_);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_sub(v_nargs_802_, v___x_808_);
lean_dec(v_nargs_802_);
v___x_810_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_778_, v___x_807_, v___x_809_);
lean_inc(v_nargs_803_);
v___x_811_ = lean_mk_array(v_nargs_803_, v_dummy_806_);
v___x_812_ = lean_nat_sub(v_nargs_803_, v___x_808_);
lean_dec(v_nargs_803_);
v___x_813_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_713_, v___x_811_, v___x_812_);
v___x_814_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_804_, v___x_810_, v___x_813_, v_ctor_731_, v_numParams_793_, v___x_805_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec(v___x_804_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_828_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_828_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_fst_819_; 
v_fst_819_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_fst_819_);
lean_dec(v_a_815_);
if (lean_obj_tag(v_fst_819_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_box(v___x_725_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; 
v_val_824_ = lean_ctor_get(v_fst_819_, 0);
lean_inc(v_val_824_);
lean_dec_ref(v_fst_819_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_val_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_814_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_814_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_numFields_794_);
lean_dec(v_numParams_793_);
lean_dec_ref(v_self_778_);
lean_dec_ref(v_rhs_713_);
v___x_837_ = lean_box(v_ctor_731_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_837_);
v___x_839_ = v___x_788_;
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
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec(v_a_786_);
lean_dec(v_val_784_);
lean_dec_ref(v_self_778_);
lean_dec_ref(v_rhs_713_);
v___x_841_ = lean_box(v___x_725_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_841_);
v___x_843_ = v___x_788_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_val_784_);
lean_dec_ref(v_self_778_);
lean_dec_ref(v_rhs_713_);
v_a_846_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_785_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_785_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_a_780_);
lean_dec_ref(v_self_778_);
lean_dec_ref(v_rhs_713_);
v___x_854_ = lean_box(v___x_725_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_854_);
v___x_856_ = v___x_782_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
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
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref(v_self_778_);
lean_dec_ref(v_rhs_713_);
v_a_859_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_779_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_779_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
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
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v_rhs_713_);
v_a_868_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_726_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_726_);
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
else
{
uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v_rhs_713_);
lean_dec_ref(v_lhs_712_);
v___x_876_ = 0;
v___x_877_ = lean_box(v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_879_, lean_object* v___x_880_, lean_object* v___x_881_, uint8_t v___x_882_, lean_object* v_a_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_nat_dec_lt(v_a_883_, v_upperBound_879_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec(v_a_883_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_b_884_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v_b_884_);
v___x_898_ = l_Lean_instInhabitedExpr;
v___x_899_ = lean_array_get_borrowed(v___x_898_, v___x_880_, v_a_883_);
v___x_900_ = lean_array_get_borrowed(v___x_898_, v___x_881_, v_a_883_);
lean_inc(v___x_900_);
lean_inc(v___x_899_);
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_899_, v___x_900_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_918_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_918_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_918_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_918_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_box(0);
v___x_907_ = lean_unbox(v_a_902_);
lean_dec(v_a_902_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_del_object(v___x_904_);
v___x_908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_nat_add(v_a_883_, v___x_909_);
lean_dec(v_a_883_);
v_a_883_ = v___x_910_;
v_b_884_ = v___x_908_;
goto _start;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
lean_dec(v_a_883_);
v___x_912_ = lean_box(v___x_882_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_906_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_914_);
v___x_916_ = v___x_904_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_883_);
v_a_919_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_901_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_901_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_927_ = _args[0];
lean_object* v___x_928_ = _args[1];
lean_object* v___x_929_ = _args[2];
lean_object* v___x_930_ = _args[3];
lean_object* v_a_931_ = _args[4];
lean_object* v_b_932_ = _args[5];
lean_object* v___y_933_ = _args[6];
lean_object* v___y_934_ = _args[7];
lean_object* v___y_935_ = _args[8];
lean_object* v___y_936_ = _args[9];
lean_object* v___y_937_ = _args[10];
lean_object* v___y_938_ = _args[11];
lean_object* v___y_939_ = _args[12];
lean_object* v___y_940_ = _args[13];
lean_object* v___y_941_ = _args[14];
lean_object* v___y_942_ = _args[15];
lean_object* v___y_943_ = _args[16];
_start:
{
uint8_t v___x_28909__boxed_944_; lean_object* v_res_945_; 
v___x_28909__boxed_944_ = lean_unbox(v___x_930_);
v_res_945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_927_, v___x_928_, v___x_929_, v___x_28909__boxed_944_, v_a_931_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_928_);
lean_dec(v_upperBound_927_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_lhs_946_, lean_object* v_rhs_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_946_, v_rhs_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec(v_a_948_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_960_, lean_object* v___x_961_, lean_object* v___x_962_, uint8_t v___x_963_, lean_object* v_inst_964_, lean_object* v_R_965_, lean_object* v_a_966_, lean_object* v_b_967_, lean_object* v_c_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_960_, v___x_961_, v___x_962_, v___x_963_, v_a_966_, v_b_967_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_981_ = _args[0];
lean_object* v___x_982_ = _args[1];
lean_object* v___x_983_ = _args[2];
lean_object* v___x_984_ = _args[3];
lean_object* v_inst_985_ = _args[4];
lean_object* v_R_986_ = _args[5];
lean_object* v_a_987_ = _args[6];
lean_object* v_b_988_ = _args[7];
lean_object* v_c_989_ = _args[8];
lean_object* v___y_990_ = _args[9];
lean_object* v___y_991_ = _args[10];
lean_object* v___y_992_ = _args[11];
lean_object* v___y_993_ = _args[12];
lean_object* v___y_994_ = _args[13];
lean_object* v___y_995_ = _args[14];
lean_object* v___y_996_ = _args[15];
lean_object* v___y_997_ = _args[16];
lean_object* v___y_998_ = _args[17];
lean_object* v___y_999_ = _args[18];
lean_object* v___y_1000_ = _args[19];
_start:
{
uint8_t v___x_29305__boxed_1001_; lean_object* v_res_1002_; 
v___x_29305__boxed_1001_ = lean_unbox(v___x_984_);
v_res_1002_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_981_, v___x_982_, v___x_983_, v___x_29305__boxed_1001_, v_inst_985_, v_R_986_, v_a_987_, v_b_988_, v_c_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_982_);
lean_dec(v_upperBound_981_);
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
lean_dec_ref(v___x_1015_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_options_1043_; uint8_t v_hasTrace_1044_; 
v_options_1043_ = lean_ctor_get(v___y_1041_, 2);
v_hasTrace_1044_ = lean_ctor_get_uint8(v_options_1043_, sizeof(void*)*1);
if (v_hasTrace_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v_cls_1040_);
v___x_1045_ = lean_box(v_hasTrace_1044_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v_inheritedTraceOptions_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_inheritedTraceOptions_1047_ = lean_ctor_get(v___y_1041_, 13);
v___x_1048_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1049_ = l_Lean_Name_append(v___x_1048_, v_cls_1040_);
v___x_1050_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1047_, v_options_1043_, v___x_1049_);
lean_dec(v___x_1049_);
v___x_1051_ = lean_box(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1053_, v___y_1054_);
lean_dec_ref(v___y_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1057_, v___y_1066_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec(v___y_1071_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(lean_object* v_msgData_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v_env_1090_; lean_object* v___x_1091_; lean_object* v_mctx_1092_; lean_object* v_lctx_1093_; lean_object* v_options_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1089_ = lean_st_ref_get(v___y_1087_);
v_env_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_env_1090_);
lean_dec(v___x_1089_);
v___x_1091_ = lean_st_ref_get(v___y_1085_);
v_mctx_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_mctx_1092_);
lean_dec(v___x_1091_);
v_lctx_1093_ = lean_ctor_get(v___y_1084_, 2);
v_options_1094_ = lean_ctor_get(v___y_1086_, 2);
lean_inc_ref(v_options_1094_);
lean_inc_ref(v_lctx_1093_);
v___x_1095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1095_, 0, v_env_1090_);
lean_ctor_set(v___x_1095_, 1, v_mctx_1092_);
lean_ctor_set(v___x_1095_, 2, v_lctx_1093_);
lean_ctor_set(v___x_1095_, 3, v_options_1094_);
v___x_1096_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_msgData_1083_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1___boxed(lean_object* v_msgData_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(v_msgData_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1104_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1105_; double v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_float_of_nat(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(lean_object* v_cls_1110_, lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1163_; 
v_ref_1117_ = lean_ctor_get(v___y_1114_, 5);
v___x_1118_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(v_msg_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1163_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1163_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v_traceState_1124_; lean_object* v_env_1125_; lean_object* v_nextMacroScope_1126_; lean_object* v_ngen_1127_; lean_object* v_auxDeclNGen_1128_; lean_object* v_cache_1129_; lean_object* v_messages_1130_; lean_object* v_infoState_1131_; lean_object* v_snapshotTasks_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1162_; 
v___x_1123_ = lean_st_ref_take(v___y_1115_);
v_traceState_1124_ = lean_ctor_get(v___x_1123_, 4);
v_env_1125_ = lean_ctor_get(v___x_1123_, 0);
v_nextMacroScope_1126_ = lean_ctor_get(v___x_1123_, 1);
v_ngen_1127_ = lean_ctor_get(v___x_1123_, 2);
v_auxDeclNGen_1128_ = lean_ctor_get(v___x_1123_, 3);
v_cache_1129_ = lean_ctor_get(v___x_1123_, 5);
v_messages_1130_ = lean_ctor_get(v___x_1123_, 6);
v_infoState_1131_ = lean_ctor_get(v___x_1123_, 7);
v_snapshotTasks_1132_ = lean_ctor_get(v___x_1123_, 8);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1134_ = v___x_1123_;
v_isShared_1135_ = v_isSharedCheck_1162_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snapshotTasks_1132_);
lean_inc(v_infoState_1131_);
lean_inc(v_messages_1130_);
lean_inc(v_cache_1129_);
lean_inc(v_traceState_1124_);
lean_inc(v_auxDeclNGen_1128_);
lean_inc(v_ngen_1127_);
lean_inc(v_nextMacroScope_1126_);
lean_inc(v_env_1125_);
lean_dec(v___x_1123_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1162_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint64_t v_tid_1136_; lean_object* v_traces_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1161_; 
v_tid_1136_ = lean_ctor_get_uint64(v_traceState_1124_, sizeof(void*)*1);
v_traces_1137_ = lean_ctor_get(v_traceState_1124_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_traceState_1124_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1139_ = v_traceState_1124_;
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_traces_1137_);
lean_dec(v_traceState_1124_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; double v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0);
v___x_1143_ = 0;
v___x_1144_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1));
v___x_1145_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1145_, 0, v_cls_1110_);
lean_ctor_set(v___x_1145_, 1, v___x_1141_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
lean_ctor_set_float(v___x_1145_, sizeof(void*)*3, v___x_1142_);
lean_ctor_set_float(v___x_1145_, sizeof(void*)*3 + 8, v___x_1142_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3 + 16, v___x_1143_);
v___x_1146_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2));
v___x_1147_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v_a_1119_);
lean_ctor_set(v___x_1147_, 2, v___x_1146_);
lean_inc(v_ref_1117_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_ref_1117_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_PersistentArray_push___redArg(v_traces_1137_, v___x_1148_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1149_);
v___x_1151_ = v___x_1139_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1149_);
lean_ctor_set_uint64(v_reuseFailAlloc_1160_, sizeof(void*)*1, v_tid_1136_);
v___x_1151_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v___x_1151_);
v___x_1153_ = v___x_1134_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_env_1125_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_nextMacroScope_1126_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_ngen_1127_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_auxDeclNGen_1128_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_cache_1129_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_messages_1130_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v_infoState_1131_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_snapshotTasks_1132_);
v___x_1153_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_st_ref_set(v___y_1115_, v___x_1153_);
v___x_1155_ = lean_box(0);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1155_);
v___x_1157_ = v___x_1121_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v_cls_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_1164_, v_msg_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1171_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__4));
v___x_1181_ = l_Lean_stringToMessageData(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__6));
v___x_1184_ = l_Lean_stringToMessageData(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(uint8_t v___x_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1264_; 
v_snd_1198_ = lean_ctor_get(v_b_1186_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_b_1186_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v_b_1186_, 0);
lean_dec(v_unused_1265_);
v___x_1200_ = v_b_1186_;
v_isShared_1201_ = v_isSharedCheck_1264_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_dec(v_b_1186_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1264_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_box(0);
if (lean_obj_tag(v_snd_1198_) == 7)
{
lean_object* v_binderType_1210_; lean_object* v_body_1211_; lean_object* v___x_1212_; 
v_binderType_1210_ = lean_ctor_get(v_snd_1198_, 1);
v_body_1211_ = lean_ctor_get(v_snd_1198_, 2);
lean_inc_ref(v_binderType_1210_);
v___x_1212_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1210_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; uint8_t v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_inc_ref(v_body_1211_);
lean_dec_ref(v_snd_1198_);
lean_del_object(v___x_1200_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1209_);
lean_ctor_set(v___x_1215_, 1, v_body_1211_);
v_b_1186_ = v___x_1215_;
goto _start;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_1218_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1217_, v___y_1195_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; uint8_t v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = lean_unbox(v_a_1219_);
lean_dec(v_a_1219_);
if (v___x_1220_ == 0)
{
goto v___jp_1202_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_Grind_updateLastTag(v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1221_);
v___x_1222_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5);
lean_inc_ref(v_snd_1198_);
v___x_1223_ = l_Lean_indentExpr(v_snd_1198_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_inc_ref(v_binderType_1210_);
v___x_1227_ = l_Lean_indentExpr(v_binderType_1210_);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1217_, v___x_1228_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_dec_ref(v___x_1229_);
goto v___jp_1202_;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_snd_1198_);
lean_del_object(v___x_1200_);
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v_snd_1198_);
lean_del_object(v___x_1200_);
v_a_1238_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1221_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1221_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_snd_1198_);
lean_del_object(v___x_1200_);
v_a_1246_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1218_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1218_);
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
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_snd_1198_);
lean_del_object(v___x_1200_);
v_a_1254_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1212_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1212_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_del_object(v___x_1200_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1209_);
lean_ctor_set(v___x_1262_, 1, v_snd_1198_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
v___jp_1202_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_box(v___x_1185_);
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1204_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_snd_1198_);
v___x_1206_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___boxed(lean_object* v___x_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_27212__boxed_1279_; lean_object* v_res_1280_; 
v___x_27212__boxed_1279_ = lean_unbox(v___x_1266_);
v_res_1280_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(v___x_27212__boxed_1279_, v_b_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1281_, v_a_1289_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1336_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1336_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1336_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = l_Lean_Expr_cleanupAnnotations(v_a_1294_);
v___x_1305_ = l_Lean_Expr_isApp(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v___x_1304_);
goto v___jp_1298_;
}
else
{
lean_object* v_arg_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_arg_1306_ = lean_ctor_get(v___x_1304_, 1);
lean_inc_ref(v_arg_1306_);
v___x_1307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1304_);
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1309_ = l_Lean_Expr_isConstOf(v___x_1307_, v___x_1308_);
lean_dec_ref(v___x_1307_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v_arg_1306_);
goto v___jp_1298_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_del_object(v___x_1296_);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_arg_1306_);
v___x_1312_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(v___x_1309_, v___x_1311_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1327_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1327_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1327_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_fst_1317_; 
v_fst_1317_ = lean_ctor_get(v_a_1313_, 0);
lean_inc(v_fst_1317_);
lean_dec(v_a_1313_);
if (lean_obj_tag(v_fst_1317_) == 0)
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
else
{
lean_object* v_val_1323_; lean_object* v___x_1325_; 
v_val_1323_ = lean_ctor_get(v_fst_1317_, 0);
lean_inc(v_val_1323_);
lean_dec_ref(v_fst_1317_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v_val_1323_);
v___x_1325_ = v___x_1315_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_val_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1328_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1312_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1312_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
v___jp_1298_:
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = 0;
v___x_1300_ = lean_box(v___x_1299_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1300_);
v___x_1302_ = v___x_1296_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1293_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1293_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec(v_a_1346_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(lean_object* v_cls_1358_, lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_1358_, v_msg_1359_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v_cls_1372_, lean_object* v_msg_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v_cls_1372_, v_msg_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1374_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v_b_1393_, lean_object* v_c_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc(v___y_1387_);
v___x_1400_ = lean_apply_13(v_k_1386_, v_b_1393_, v_c_1394_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, lean_box(0));
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v_b_1408_, lean_object* v_c_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v_b_1408_, v_c_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec(v___y_1402_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1416_, lean_object* v_k_1417_, uint8_t v_cleanupAnnotations_1418_, uint8_t v_whnfType_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___f_1431_; lean_object* v___x_1432_; 
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1421_);
lean_inc(v___y_1420_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1431_, 0, v_k_1417_);
lean_closure_set(v___f_1431_, 1, v___y_1420_);
lean_closure_set(v___f_1431_, 2, v___y_1421_);
lean_closure_set(v___f_1431_, 3, v___y_1422_);
lean_closure_set(v___f_1431_, 4, v___y_1423_);
lean_closure_set(v___f_1431_, 5, v___y_1424_);
lean_closure_set(v___f_1431_, 6, v___y_1425_);
v___x_1432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1416_, v___f_1431_, v_cleanupAnnotations_1418_, v_whnfType_1419_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1432_) == 0)
{
return v___x_1432_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1441_, lean_object* v_k_1442_, lean_object* v_cleanupAnnotations_1443_, lean_object* v_whnfType_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1456_; uint8_t v_whnfType_boxed_1457_; lean_object* v_res_1458_; 
v_cleanupAnnotations_boxed_1456_ = lean_unbox(v_cleanupAnnotations_1443_);
v_whnfType_boxed_1457_ = lean_unbox(v_whnfType_1444_);
v_res_1458_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1441_, v_k_1442_, v_cleanupAnnotations_boxed_1456_, v_whnfType_boxed_1457_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v___y_1445_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1459_, lean_object* v_type_1460_, lean_object* v_k_1461_, uint8_t v_cleanupAnnotations_1462_, uint8_t v_whnfType_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1460_, v_k_1461_, v_cleanupAnnotations_1462_, v_whnfType_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1476_, lean_object* v_type_1477_, lean_object* v_k_1478_, lean_object* v_cleanupAnnotations_1479_, lean_object* v_whnfType_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1492_; uint8_t v_whnfType_boxed_1493_; lean_object* v_res_1494_; 
v_cleanupAnnotations_boxed_1492_ = lean_unbox(v_cleanupAnnotations_1479_);
v_whnfType_boxed_1493_ = lean_unbox(v_whnfType_1480_);
v_res_1494_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1476_, v_type_1477_, v_k_1478_, v_cleanupAnnotations_boxed_1492_, v_whnfType_boxed_1493_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec(v___y_1481_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* v_e_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_xs_1501_, lean_object* v_x_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
uint8_t v_a_111511__boxed_1514_; lean_object* v_res_1515_; 
v_a_111511__boxed_1514_ = lean_unbox(v_a_1499_);
v_res_1515_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1498_, v_a_111511__boxed_1514_, v_a_1500_, v_xs_1501_, v_x_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v_x_1502_);
lean_dec_ref(v_xs_1501_);
return v_res_1515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1521_ = l_Lean_stringToMessageData(v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1525_, lean_object* v_h_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
uint8_t v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; uint8_t v___y_1546_; lean_object* v___y_1547_; lean_object* v_h_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v_cls_1928_; lean_object* v___x_1929_; 
v_cls_1928_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_1929_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1928_, v_a_1535_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; uint8_t v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v___x_1931_ = lean_unbox(v_a_1930_);
lean_dec(v_a_1930_);
if (v___x_1931_ == 0)
{
v___y_1812_ = v_a_1527_;
v___y_1813_ = v_a_1528_;
v___y_1814_ = v_a_1529_;
v___y_1815_ = v_a_1530_;
v___y_1816_ = v_a_1531_;
v___y_1817_ = v_a_1532_;
v___y_1818_ = v_a_1533_;
v___y_1819_ = v_a_1534_;
v___y_1820_ = v_a_1535_;
v___y_1821_ = v_a_1536_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Meta_Grind_updateLastTag(v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref(v___x_1932_);
lean_inc(v_a_1536_);
lean_inc_ref(v_a_1535_);
lean_inc(v_a_1534_);
lean_inc_ref(v_a_1533_);
lean_inc_ref(v_h_1526_);
v___x_1933_ = lean_infer_type(v_h_1526_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1936_ = l_Lean_MessageData_ofExpr(v_a_1934_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_1928_, v___x_1937_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_dec_ref(v___x_1938_);
v___y_1812_ = v_a_1527_;
v___y_1813_ = v_a_1528_;
v___y_1814_ = v_a_1529_;
v___y_1815_ = v_a_1530_;
v___y_1816_ = v_a_1531_;
v___y_1817_ = v_a_1532_;
v___y_1818_ = v_a_1533_;
v___y_1819_ = v_a_1534_;
v___y_1820_ = v_a_1535_;
v___y_1821_ = v_a_1536_;
goto v___jp_1811_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1947_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1933_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1933_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1955_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1932_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1932_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1963_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1929_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1929_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
v___jp_1538_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
v___jp_1541_:
{
if (v___y_1546_ == 0)
{
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_e_1525_);
if (v___y_1545_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v___y_1544_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; 
lean_inc_ref(v___y_1547_);
v___x_1561_ = l_Lean_Meta_normLitValue(v___y_1547_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
lean_inc_ref(v___y_1544_);
v___x_1563_ = l_Lean_Meta_normLitValue(v___y_1544_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1603_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1603_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1603_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
uint8_t v___x_1568_; 
v___x_1568_ = lean_expr_eqv(v_a_1562_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec(v_a_1562_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_del_object(v___x_1566_);
v___x_1569_ = l_Lean_Meta_mkEq(v___y_1547_, v___y_1544_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = l_Lean_mkNot(v_a_1570_);
v___x_1572_ = l_Lean_Meta_mkDecideProof(v___x_1571_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1582_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1582_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1582_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1577_ = l_Lean_Expr_app___override(v_a_1573_, v_h_1548_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_h_1548_);
v_a_1583_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1572_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1572_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_h_1548_);
v_a_1591_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1569_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1569_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v___y_1544_);
v___x_1599_ = lean_box(0);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1599_);
v___x_1601_ = v___x_1566_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1562_);
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v___y_1544_);
v_a_1604_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1563_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1563_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v___y_1544_);
v_a_1612_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1561_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1561_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1547_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1711_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1711_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1711_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
if (lean_obj_tag(v_a_1621_) == 1)
{
lean_object* v_val_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1623_);
v_val_1625_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_val_1625_);
lean_dec_ref(v_a_1621_);
v___x_1626_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1544_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1698_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1698_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1698_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
if (lean_obj_tag(v_a_1627_) == 1)
{
lean_object* v_val_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1693_; 
lean_del_object(v___x_1629_);
v_val_1631_ = lean_ctor_get(v_a_1627_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1627_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1633_ = v_a_1627_;
v_isShared_1634_ = v_isSharedCheck_1693_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_val_1631_);
lean_dec(v_a_1627_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1693_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Meta_mkNoConfusion(v___y_1543_, v_h_1548_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_toConstantVal_1636_; lean_object* v_toConstantVal_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1684_; 
v_toConstantVal_1636_ = lean_ctor_get(v_val_1625_, 0);
lean_inc_ref(v_toConstantVal_1636_);
lean_dec(v_val_1625_);
v_toConstantVal_1637_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_toConstantVal_1637_);
lean_dec(v_val_1631_);
v_a_1638_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1640_ = v___x_1635_;
v_isShared_1641_ = v_isSharedCheck_1684_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1684_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_name_1642_; lean_object* v_name_1643_; uint8_t v___x_1644_; 
v_name_1642_ = lean_ctor_get(v_toConstantVal_1636_, 0);
lean_inc(v_name_1642_);
lean_dec_ref(v_toConstantVal_1636_);
v_name_1643_ = lean_ctor_get(v_toConstantVal_1637_, 0);
lean_inc(v_name_1643_);
lean_dec_ref(v_toConstantVal_1637_);
v___x_1644_ = lean_name_eq(v_name_1642_, v_name_1643_);
lean_dec(v_name_1643_);
lean_dec(v_name_1642_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v_e_1525_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_a_1638_);
v___x_1646_ = v___x_1633_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1638_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1646_);
v___x_1648_ = v___x_1640_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v___x_1651_; 
lean_del_object(v___x_1640_);
lean_del_object(v___x_1633_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v_a_1638_);
v___x_1651_ = lean_infer_type(v_a_1638_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = l_Lean_Meta_whnfD(v_a_1652_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1667_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1667_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1667_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
if (lean_obj_tag(v_a_1654_) == 7)
{
lean_object* v_binderType_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; 
lean_del_object(v___x_1656_);
v_binderType_1658_ = lean_ctor_get(v_a_1654_, 1);
lean_inc_ref(v_binderType_1658_);
lean_dec_ref(v_a_1654_);
v___x_1659_ = lean_box(v___y_1542_);
v___f_1660_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1660_, 0, v_e_1525_);
lean_closure_set(v___f_1660_, 1, v___x_1659_);
lean_closure_set(v___f_1660_, 2, v_a_1638_);
v___x_1661_ = 0;
v___x_1662_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1658_, v___f_1660_, v___x_1661_, v___x_1661_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_dec(v_a_1654_);
lean_dec(v_a_1638_);
lean_dec_ref(v_e_1525_);
v___x_1663_ = lean_box(0);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1663_);
v___x_1665_ = v___x_1656_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
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
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_a_1638_);
lean_dec_ref(v_e_1525_);
v_a_1668_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1653_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1653_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_a_1638_);
lean_dec_ref(v_e_1525_);
v_a_1676_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1651_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1651_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1633_);
lean_dec(v_val_1631_);
lean_dec(v_val_1625_);
lean_dec_ref(v_e_1525_);
v_a_1685_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1635_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1635_);
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
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_dec(v_a_1627_);
lean_dec(v_val_1625_);
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_e_1525_);
v___x_1694_ = lean_box(0);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1694_);
v___x_1696_ = v___x_1629_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_val_1625_);
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_e_1525_);
v_a_1699_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1626_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1626_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
lean_dec(v_a_1621_);
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_e_1525_);
v___x_1707_ = lean_box(0);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1707_);
v___x_1709_ = v___x_1623_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_h_1548_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_e_1525_);
v_a_1712_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1620_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1620_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
v___jp_1720_:
{
lean_object* v_self_1736_; uint8_t v_interpreted_1737_; uint8_t v_ctor_1738_; lean_object* v___x_1739_; 
v_self_1736_ = lean_ctor_get(v___y_1729_, 0);
lean_inc_ref(v_self_1736_);
v_interpreted_1737_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*11 + 1);
v_ctor_1738_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*11 + 2);
lean_dec_ref(v___y_1729_);
lean_inc_ref(v___y_1724_);
lean_inc_ref(v_self_1736_);
v___x_1739_ = l_Lean_Meta_Grind_hasSameType(v_self_1736_, v___y_1724_, v___y_1728_, v___y_1726_, v___y_1730_, v___y_1727_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1802_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1802_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1802_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_unbox(v_a_1740_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec(v_a_1740_);
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v___x_1745_ = lean_box(0);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1745_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
else
{
lean_del_object(v___x_1742_);
if (v___y_1735_ == 0)
{
lean_object* v___x_1749_; 
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1728_);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1723_);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1722_);
lean_inc(v___y_1734_);
lean_inc_ref(v_self_1736_);
v___x_1749_ = lean_grind_mk_eq_proof(v_self_1736_, v___y_1731_, v___y_1734_, v___y_1722_, v___y_1732_, v___y_1733_, v___y_1723_, v___y_1725_, v___y_1728_, v___y_1726_, v___y_1730_, v___y_1727_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = l_Lean_Meta_mkEqTrans(v_a_1750_, v_h_1526_, v___y_1728_, v___y_1726_, v___y_1730_, v___y_1727_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; uint8_t v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_unbox(v_a_1740_);
lean_dec(v_a_1740_);
v___y_1542_ = v___x_1753_;
v___y_1543_ = v___y_1721_;
v___y_1544_ = v___y_1724_;
v___y_1545_ = v_interpreted_1737_;
v___y_1546_ = v_ctor_1738_;
v___y_1547_ = v_self_1736_;
v_h_1548_ = v_a_1752_;
v___y_1549_ = v___y_1734_;
v___y_1550_ = v___y_1722_;
v___y_1551_ = v___y_1732_;
v___y_1552_ = v___y_1733_;
v___y_1553_ = v___y_1723_;
v___y_1554_ = v___y_1725_;
v___y_1555_ = v___y_1728_;
v___y_1556_ = v___y_1726_;
v___y_1557_ = v___y_1730_;
v___y_1558_ = v___y_1727_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1740_);
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_e_1525_);
v_a_1754_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1751_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1751_);
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
lean_dec(v_a_1740_);
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1762_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1749_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1749_);
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
else
{
lean_object* v___x_1770_; 
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1728_);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1723_);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1722_);
lean_inc(v___y_1734_);
lean_inc_ref(v_self_1736_);
v___x_1770_ = lean_grind_mk_heq_proof(v_self_1736_, v___y_1731_, v___y_1734_, v___y_1722_, v___y_1732_, v___y_1733_, v___y_1723_, v___y_1725_, v___y_1728_, v___y_1726_, v___y_1730_, v___y_1727_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = l_Lean_Meta_mkHEqTrans(v_a_1771_, v_h_1526_, v___y_1728_, v___y_1726_, v___y_1730_, v___y_1727_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = 0;
v___x_1775_ = l_Lean_Meta_mkEqOfHEq(v_a_1773_, v___x_1774_, v___y_1728_, v___y_1726_, v___y_1730_, v___y_1727_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; uint8_t v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = lean_unbox(v_a_1740_);
lean_dec(v_a_1740_);
v___y_1542_ = v___x_1777_;
v___y_1543_ = v___y_1721_;
v___y_1544_ = v___y_1724_;
v___y_1545_ = v_interpreted_1737_;
v___y_1546_ = v_ctor_1738_;
v___y_1547_ = v_self_1736_;
v_h_1548_ = v_a_1776_;
v___y_1549_ = v___y_1734_;
v___y_1550_ = v___y_1722_;
v___y_1551_ = v___y_1732_;
v___y_1552_ = v___y_1733_;
v___y_1553_ = v___y_1723_;
v___y_1554_ = v___y_1725_;
v___y_1555_ = v___y_1728_;
v___y_1556_ = v___y_1726_;
v___y_1557_ = v___y_1730_;
v___y_1558_ = v___y_1727_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1740_);
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_e_1525_);
v_a_1778_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1775_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1775_);
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
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_a_1740_);
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_e_1525_);
v_a_1786_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1772_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1772_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1740_);
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1794_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1770_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1770_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_self_1736_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1803_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1739_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1739_);
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
v___jp_1811_:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1821_);
lean_inc_ref(v___y_1820_);
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc_ref(v_h_1526_);
v___x_1822_ = lean_infer_type(v_h_1526_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1919_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1919_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1919_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1823_);
if (lean_obj_tag(v___x_1827_) == 1)
{
lean_object* v_val_1828_; lean_object* v_snd_1829_; lean_object* v_fst_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1914_; 
lean_del_object(v___x_1825_);
v_val_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref(v___x_1827_);
v_snd_1829_ = lean_ctor_get(v_val_1828_, 1);
v_fst_1830_ = lean_ctor_get(v_val_1828_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_val_1828_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1832_ = v_val_1828_;
v_isShared_1833_ = v_isSharedCheck_1914_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1829_);
lean_inc(v_fst_1830_);
lean_dec(v_val_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1914_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_fst_1834_; lean_object* v_snd_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1913_; 
v_fst_1834_ = lean_ctor_get(v_snd_1829_, 0);
v_snd_1835_ = lean_ctor_get(v_snd_1829_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_snd_1829_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1837_ = v_snd_1829_;
v_isShared_1838_ = v_isSharedCheck_1913_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_snd_1835_);
lean_inc(v_fst_1834_);
lean_dec(v_snd_1829_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1913_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v_mvarId_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1911_; 
v___x_1839_ = lean_st_ref_get(v___y_1812_);
v_mvarId_1840_ = lean_ctor_get(v___x_1839_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1839_, 0);
lean_dec(v_unused_1912_);
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1911_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_mvarId_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1911_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_MVarId_getType(v_mvarId_1840_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_1834_, v___y_1817_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1847_, v___y_1812_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
if (lean_obj_tag(v_a_1849_) == 1)
{
lean_del_object(v___x_1842_);
lean_del_object(v___x_1837_);
lean_del_object(v___x_1832_);
if (lean_obj_tag(v_fst_1830_) == 0)
{
lean_object* v_val_1850_; uint8_t v___x_1851_; 
v_val_1850_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_val_1850_);
lean_dec_ref(v_a_1849_);
v___x_1851_ = 0;
v___y_1721_ = v_a_1845_;
v___y_1722_ = v___y_1813_;
v___y_1723_ = v___y_1816_;
v___y_1724_ = v_snd_1835_;
v___y_1725_ = v___y_1817_;
v___y_1726_ = v___y_1819_;
v___y_1727_ = v___y_1821_;
v___y_1728_ = v___y_1818_;
v___y_1729_ = v_val_1850_;
v___y_1730_ = v___y_1820_;
v___y_1731_ = v_a_1847_;
v___y_1732_ = v___y_1814_;
v___y_1733_ = v___y_1815_;
v___y_1734_ = v___y_1812_;
v___y_1735_ = v___x_1851_;
goto v___jp_1720_;
}
else
{
lean_object* v_val_1852_; uint8_t v___x_1853_; 
lean_dec_ref(v_fst_1830_);
v_val_1852_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_val_1852_);
lean_dec_ref(v_a_1849_);
v___x_1853_ = 1;
v___y_1721_ = v_a_1845_;
v___y_1722_ = v___y_1813_;
v___y_1723_ = v___y_1816_;
v___y_1724_ = v_snd_1835_;
v___y_1725_ = v___y_1817_;
v___y_1726_ = v___y_1819_;
v___y_1727_ = v___y_1821_;
v___y_1728_ = v___y_1818_;
v___y_1729_ = v_val_1852_;
v___y_1730_ = v___y_1820_;
v___y_1731_ = v_a_1847_;
v___y_1732_ = v___y_1814_;
v___y_1733_ = v___y_1815_;
v___y_1734_ = v___y_1812_;
v___y_1735_ = v___x_1853_;
goto v___jp_1720_;
}
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_a_1849_);
lean_dec(v_a_1845_);
lean_dec(v_snd_1835_);
lean_dec(v_fst_1830_);
lean_dec_ref(v_h_1526_);
v___x_1854_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_1814_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; uint8_t v_verbose_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v_verbose_1856_ = lean_ctor_get_uint8(v_a_1855_, sizeof(void*)*11 + 15);
lean_dec(v_a_1855_);
if (v_verbose_1856_ == 0)
{
lean_dec(v_a_1847_);
lean_del_object(v___x_1842_);
lean_del_object(v___x_1837_);
lean_del_object(v___x_1832_);
lean_dec_ref(v_e_1525_);
goto v___jp_1538_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1858_ = l_Lean_indentExpr(v_a_1847_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 7);
lean_ctor_set(v___x_1842_, 1, v___x_1858_);
lean_ctor_set(v___x_1842_, 0, v___x_1857_);
v___x_1860_ = v___x_1842_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 7);
lean_ctor_set(v___x_1837_, 1, v___x_1861_);
lean_ctor_set(v___x_1837_, 0, v___x_1860_);
v___x_1863_ = v___x_1837_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1864_ = l_Lean_indentExpr(v_e_1525_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 7);
lean_ctor_set(v___x_1832_, 1, v___x_1864_);
lean_ctor_set(v___x_1832_, 0, v___x_1863_);
v___x_1866_ = v___x_1832_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Meta_Grind_reportIssue(v___x_1866_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_dec_ref(v___x_1867_);
goto v___jp_1538_;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
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
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1847_);
lean_del_object(v___x_1842_);
lean_del_object(v___x_1837_);
lean_del_object(v___x_1832_);
lean_dec_ref(v_e_1525_);
v_a_1879_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1854_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1854_);
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
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_a_1847_);
lean_dec(v_a_1845_);
lean_del_object(v___x_1842_);
lean_del_object(v___x_1837_);
lean_dec(v_snd_1835_);
lean_del_object(v___x_1832_);
lean_dec(v_fst_1830_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1887_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1848_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1848_);
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
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1845_);
lean_del_object(v___x_1842_);
lean_del_object(v___x_1837_);
lean_dec(v_snd_1835_);
lean_del_object(v___x_1832_);
lean_dec(v_fst_1830_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1895_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1846_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1846_);
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
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_del_object(v___x_1842_);
lean_del_object(v___x_1837_);
lean_dec(v_snd_1835_);
lean_dec(v_fst_1834_);
lean_del_object(v___x_1832_);
lean_dec(v_fst_1830_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1903_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1844_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1844_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v___x_1827_);
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v___x_1915_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1915_);
v___x_1917_ = v___x_1825_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v_h_1526_);
lean_dec_ref(v_e_1525_);
v_a_1920_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1822_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1822_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_1971_, lean_object* v_xs_1972_, uint8_t v_a_1973_, lean_object* v_a_1974_, lean_object* v_as_1975_, size_t v_sz_1976_, size_t v_i_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_usize_dec_lt(v_i_1977_, v_sz_1976_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec_ref(v_a_1974_);
lean_dec_ref(v_e_1971_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v_b_1978_);
return v___x_1991_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
lean_dec_ref(v_b_1978_);
v_a_1992_ = lean_array_uget_borrowed(v_as_1975_, v_i_1977_);
lean_inc(v_a_1992_);
lean_inc_ref(v_e_1971_);
v___x_1993_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_1971_, v_a_1992_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref(v___x_1993_);
v___x_1995_ = lean_box(0);
if (lean_obj_tag(v_a_1994_) == 1)
{
lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_e_1971_);
v_val_1996_ = lean_ctor_get(v_a_1994_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1998_ = v_a_1994_;
v_isShared_1999_ = v_isSharedCheck_2025_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v_a_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2025_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
uint8_t v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = 0;
v___x_2001_ = 1;
v___x_2002_ = l_Lean_Meta_mkLambdaFVars(v_xs_1972_, v_val_1996_, v___x_2000_, v_a_1973_, v___x_2000_, v_a_1973_, v___x_2001_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2016_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2016_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2016_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = l_Lean_Expr_app___override(v_a_1974_, v_a_2003_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2007_);
v___x_2009_ = v___x_1998_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_1995_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2011_);
v___x_2013_ = v___x_2005_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_1998_);
lean_dec_ref(v_a_1974_);
v_a_2017_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2002_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2002_);
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
}
else
{
lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; 
lean_dec(v_a_1994_);
v___x_2026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_1977_, v___x_2027_);
v_i_1977_ = v___x_2028_;
v_b_1978_ = v___x_2026_;
goto _start;
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_a_1974_);
lean_dec_ref(v_e_1971_);
v_a_2030_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1993_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1993_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2038_, uint8_t v_a_2039_, lean_object* v_a_2040_, lean_object* v_xs_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; size_t v_sz_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2056_ = lean_array_size(v_xs_2041_);
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2038_, v_xs_2041_, v_a_2039_, v_a_2040_, v_xs_2041_, v_sz_2056_, v___x_2057_, v___x_2055_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2071_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2071_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2071_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_fst_2063_; 
v_fst_2063_ = lean_ctor_get(v_a_2059_, 0);
lean_inc(v_fst_2063_);
lean_dec(v_a_2059_);
if (lean_obj_tag(v_fst_2063_) == 0)
{
lean_object* v___x_2065_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2054_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2054_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
else
{
lean_object* v_val_2067_; lean_object* v___x_2069_; 
v_val_2067_ = lean_ctor_get(v_fst_2063_, 0);
lean_inc(v_val_2067_);
lean_dec_ref(v_fst_2063_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v_val_2067_);
v___x_2069_ = v___x_2061_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_val_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_a_2072_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2058_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2058_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2080_ = _args[0];
lean_object* v_xs_2081_ = _args[1];
lean_object* v_a_2082_ = _args[2];
lean_object* v_a_2083_ = _args[3];
lean_object* v_as_2084_ = _args[4];
lean_object* v_sz_2085_ = _args[5];
lean_object* v_i_2086_ = _args[6];
lean_object* v_b_2087_ = _args[7];
lean_object* v___y_2088_ = _args[8];
lean_object* v___y_2089_ = _args[9];
lean_object* v___y_2090_ = _args[10];
lean_object* v___y_2091_ = _args[11];
lean_object* v___y_2092_ = _args[12];
lean_object* v___y_2093_ = _args[13];
lean_object* v___y_2094_ = _args[14];
lean_object* v___y_2095_ = _args[15];
lean_object* v___y_2096_ = _args[16];
lean_object* v___y_2097_ = _args[17];
lean_object* v___y_2098_ = _args[18];
_start:
{
uint8_t v_a_111535__boxed_2099_; size_t v_sz_boxed_2100_; size_t v_i_boxed_2101_; lean_object* v_res_2102_; 
v_a_111535__boxed_2099_ = lean_unbox(v_a_2082_);
v_sz_boxed_2100_ = lean_unbox_usize(v_sz_2085_);
lean_dec(v_sz_2085_);
v_i_boxed_2101_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2080_, v_xs_2081_, v_a_111535__boxed_2099_, v_a_2083_, v_as_2084_, v_sz_boxed_2100_, v_i_boxed_2101_, v_b_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v_as_2084_);
lean_dec_ref(v_xs_2081_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2103_, lean_object* v_h_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2103_, v_h_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec(v_a_2105_);
return v_res_2116_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2120_, lean_object* v_xs_2121_, uint8_t v___x_2122_, lean_object* v_as_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_a_2139_; uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
lean_dec_ref(v_e_2120_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_b_2126_);
return v___x_2144_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v_b_2126_);
v_a_2145_ = lean_array_uget_borrowed(v_as_2123_, v_i_2125_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v_a_2145_);
v___x_2146_ = lean_infer_type(v_a_2145_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2146_);
lean_inc(v_a_2147_);
v___x_2148_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2147_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; uint8_t v___x_2202_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = lean_box(0);
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2202_ = lean_unbox(v_a_2149_);
lean_dec(v_a_2149_);
if (v___x_2202_ == 0)
{
lean_dec(v_a_2147_);
v_a_2139_ = v___x_2151_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_2204_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2203_, v___y_2135_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; uint8_t v___x_2206_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = lean_unbox(v_a_2205_);
lean_dec(v_a_2205_);
if (v___x_2206_ == 0)
{
lean_dec(v_a_2147_);
v___y_2153_ = v___y_2127_;
v___y_2154_ = v___y_2128_;
v___y_2155_ = v___y_2129_;
v___y_2156_ = v___y_2130_;
v___y_2157_ = v___y_2131_;
v___y_2158_ = v___y_2132_;
v___y_2159_ = v___y_2133_;
v___y_2160_ = v___y_2134_;
v___y_2161_ = v___y_2135_;
v___y_2162_ = v___y_2136_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Meta_Grind_updateLastTag(v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v___x_2207_);
v___x_2208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2209_ = l_Lean_MessageData_ofExpr(v_a_2147_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_2203_, v___x_2210_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec_ref(v___x_2211_);
v___y_2153_ = v___y_2127_;
v___y_2154_ = v___y_2128_;
v___y_2155_ = v___y_2129_;
v___y_2156_ = v___y_2130_;
v___y_2157_ = v___y_2131_;
v___y_2158_ = v___y_2132_;
v___y_2159_ = v___y_2133_;
v___y_2160_ = v___y_2134_;
v___y_2161_ = v___y_2135_;
v___y_2162_ = v___y_2136_;
goto v___jp_2152_;
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec_ref(v_e_2120_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_a_2147_);
lean_dec_ref(v_e_2120_);
v_a_2220_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2207_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2207_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2147_);
lean_dec_ref(v_e_2120_);
v_a_2228_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2204_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2204_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
v___jp_2152_:
{
lean_object* v___x_2163_; 
lean_inc(v_a_2145_);
lean_inc_ref(v_e_2120_);
v___x_2163_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2120_, v_a_2145_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
if (lean_obj_tag(v_a_2164_) == 1)
{
lean_object* v_val_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_e_2120_);
v_val_2165_ = lean_ctor_get(v_a_2164_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_a_2164_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2167_ = v_a_2164_;
v_isShared_2168_ = v_isSharedCheck_2193_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_val_2165_);
lean_dec(v_a_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2193_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
uint8_t v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = 0;
v___x_2170_ = 1;
v___x_2171_ = l_Lean_Meta_mkLambdaFVars(v_xs_2121_, v_val_2165_, v___x_2169_, v___x_2122_, v___x_2169_, v___x_2122_, v___x_2170_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2184_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_a_2172_);
v___x_2177_ = v___x_2167_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2150_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2179_);
v___x_2181_ = v___x_2174_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_2167_);
v_a_2185_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2171_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2171_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_dec(v_a_2164_);
v_a_2139_ = v___x_2151_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v_e_2120_);
v_a_2194_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2163_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2163_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2147_);
lean_dec_ref(v_e_2120_);
v_a_2236_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2148_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2148_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_e_2120_);
v_a_2244_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2146_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2146_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
v___jp_2138_:
{
size_t v___x_2140_; size_t v___x_2141_; 
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_add(v_i_2125_, v___x_2140_);
v_i_2125_ = v___x_2141_;
v_b_2126_ = v_a_2139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2252_ = _args[0];
lean_object* v_xs_2253_ = _args[1];
lean_object* v___x_2254_ = _args[2];
lean_object* v_as_2255_ = _args[3];
lean_object* v_sz_2256_ = _args[4];
lean_object* v_i_2257_ = _args[5];
lean_object* v_b_2258_ = _args[6];
lean_object* v___y_2259_ = _args[7];
lean_object* v___y_2260_ = _args[8];
lean_object* v___y_2261_ = _args[9];
lean_object* v___y_2262_ = _args[10];
lean_object* v___y_2263_ = _args[11];
lean_object* v___y_2264_ = _args[12];
lean_object* v___y_2265_ = _args[13];
lean_object* v___y_2266_ = _args[14];
lean_object* v___y_2267_ = _args[15];
lean_object* v___y_2268_ = _args[16];
lean_object* v___y_2269_ = _args[17];
_start:
{
uint8_t v___x_26618__boxed_2270_; size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v___x_26618__boxed_2270_ = lean_unbox(v___x_2254_);
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2252_, v_xs_2253_, v___x_26618__boxed_2270_, v_as_2255_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v_as_2255_);
lean_dec_ref(v_xs_2253_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2274_, uint8_t v___x_2275_, lean_object* v_xs_2276_, lean_object* v_x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; size_t v_sz_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2291_ = lean_array_size(v_xs_2276_);
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2274_, v_xs_2276_, v___x_2275_, v_xs_2276_, v_sz_2291_, v___x_2292_, v___x_2290_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2306_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_fst_2298_; 
v_fst_2298_ = lean_ctor_get(v_a_2294_, 0);
lean_inc(v_fst_2298_);
lean_dec(v_a_2294_);
if (lean_obj_tag(v_fst_2298_) == 0)
{
lean_object* v___x_2300_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2289_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2289_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
else
{
lean_object* v_val_2302_; lean_object* v___x_2304_; 
v_val_2302_ = lean_ctor_get(v_fst_2298_, 0);
lean_inc(v_val_2302_);
lean_dec_ref(v_fst_2298_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_val_2302_);
v___x_2304_ = v___x_2296_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_val_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_a_2307_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2293_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2293_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2315_, lean_object* v___x_2316_, lean_object* v_xs_2317_, lean_object* v_x_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v___x_26888__boxed_2330_; lean_object* v_res_2331_; 
v___x_26888__boxed_2330_ = lean_unbox(v___x_2316_);
v_res_2331_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2315_, v___x_26888__boxed_2330_, v_xs_2317_, v_x_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v_x_2318_);
lean_dec_ref(v_xs_2317_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; 
lean_inc_ref(v_e_2332_);
v___x_2344_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2332_, v_a_2340_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2364_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2364_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2364_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = l_Lean_Expr_cleanupAnnotations(v_a_2345_);
v___x_2355_ = l_Lean_Expr_isApp(v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2354_);
lean_dec_ref(v_e_2332_);
goto v___jp_2349_;
}
else
{
lean_object* v_arg_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_arg_2356_ = lean_ctor_get(v___x_2354_, 1);
lean_inc_ref(v_arg_2356_);
v___x_2357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2354_);
v___x_2358_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2359_ = l_Lean_Expr_isConstOf(v___x_2357_, v___x_2358_);
lean_dec_ref(v___x_2357_);
if (v___x_2359_ == 0)
{
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_e_2332_);
goto v___jp_2349_;
}
else
{
lean_object* v___x_2360_; lean_object* v___f_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
lean_del_object(v___x_2347_);
v___x_2360_ = lean_box(v___x_2359_);
v___f_2361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2361_, 0, v_e_2332_);
lean_closure_set(v___f_2361_, 1, v___x_2360_);
v___x_2362_ = 0;
v___x_2363_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2356_, v___f_2361_, v___x_2362_, v___x_2362_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
return v___x_2363_;
}
}
v___jp_2349_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = lean_box(0);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2350_);
v___x_2352_ = v___x_2347_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_e_2332_);
v_a_2365_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2344_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2344_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec(v_a_2374_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2398_; 
lean_inc_ref(v_e_2386_);
v___x_2398_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2386_, v_a_2387_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2466_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2466_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2466_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
uint8_t v_ctor_2403_; 
v_ctor_2403_ = lean_ctor_get_uint8(v_a_2399_, sizeof(void*)*11 + 2);
if (v_ctor_2403_ == 0)
{
uint8_t v_interpreted_2404_; 
v_interpreted_2404_ = lean_ctor_get_uint8(v_a_2399_, sizeof(void*)*11 + 1);
if (v_interpreted_2404_ == 0)
{
lean_object* v___x_2406_; 
lean_dec(v_a_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v_e_2386_);
v___x_2406_ = v___x_2401_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_e_2386_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
else
{
lean_object* v_self_2408_; lean_object* v___x_2410_; 
lean_dec_ref(v_e_2386_);
v_self_2408_ = lean_ctor_get(v_a_2399_, 0);
lean_inc_ref(v_self_2408_);
lean_dec(v_a_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v_self_2408_);
v___x_2410_ = v___x_2401_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_self_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
else
{
lean_object* v_self_2412_; lean_object* v___x_2413_; 
lean_del_object(v___x_2401_);
lean_dec_ref(v_e_2386_);
v_self_2412_ = lean_ctor_get(v_a_2399_, 0);
lean_inc_ref(v_self_2412_);
lean_dec(v_a_2399_);
lean_inc_ref(v_self_2412_);
v___x_2413_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2412_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2457_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2457_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2457_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
if (lean_obj_tag(v_a_2414_) == 1)
{
lean_object* v_val_2418_; lean_object* v_numParams_2419_; lean_object* v_numFields_2420_; lean_object* v_nargs_2421_; lean_object* v___x_2422_; lean_object* v_dummy_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_del_object(v___x_2416_);
v_val_2418_ = lean_ctor_get(v_a_2414_, 0);
lean_inc(v_val_2418_);
lean_dec_ref(v_a_2414_);
v_numParams_2419_ = lean_ctor_get(v_val_2418_, 3);
lean_inc(v_numParams_2419_);
v_numFields_2420_ = lean_ctor_get(v_val_2418_, 4);
lean_inc(v_numFields_2420_);
lean_dec(v_val_2418_);
v_nargs_2421_ = l_Lean_Expr_getAppNumArgs(v_self_2412_);
v___x_2422_ = lean_nat_add(v_numParams_2419_, v_numFields_2420_);
lean_dec(v_numFields_2420_);
v_dummy_2423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2421_);
v___x_2424_ = lean_mk_array(v_nargs_2421_, v_dummy_2423_);
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_sub(v_nargs_2421_, v___x_2425_);
lean_dec(v_nargs_2421_);
lean_inc_ref(v_self_2412_);
v___x_2427_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2412_, v___x_2424_, v___x_2426_);
v___x_2428_ = 0;
v___x_2429_ = lean_box(v___x_2428_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2427_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2422_, v_ctor_2403_, v_numParams_2419_, v___x_2430_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v___x_2422_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2445_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2445_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2445_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v_snd_2436_; uint8_t v___x_2437_; 
v_snd_2436_ = lean_ctor_get(v_a_2432_, 1);
v___x_2437_ = lean_unbox(v_snd_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2439_; 
lean_dec(v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v_self_2412_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_self_2412_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
else
{
lean_object* v_fst_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_del_object(v___x_2434_);
v_fst_2441_ = lean_ctor_get(v_a_2432_, 0);
lean_inc(v_fst_2441_);
lean_dec(v_a_2432_);
v___x_2442_ = l_Lean_Expr_getAppFn(v_self_2412_);
lean_dec_ref(v_self_2412_);
v___x_2443_ = l_Lean_mkAppN(v___x_2442_, v_fst_2441_);
lean_dec(v_fst_2441_);
v___x_2444_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_2443_, v_a_2392_);
return v___x_2444_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v_self_2412_);
v_a_2446_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2431_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2431_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2455_; 
lean_dec(v_a_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_self_2412_);
v___x_2455_ = v___x_2416_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_self_2412_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v_self_2412_);
v_a_2458_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2413_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2413_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v_e_2386_);
v_a_2467_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2398_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2398_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2475_, uint8_t v___x_2476_, lean_object* v_a_2477_, lean_object* v_b_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_nat_dec_lt(v_a_2477_, v_upperBound_2475_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_a_2477_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_b_2478_);
return v___x_2491_;
}
else
{
lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2523_; 
v_fst_2492_ = lean_ctor_get(v_b_2478_, 0);
v_snd_2493_ = lean_ctor_get(v_b_2478_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_b_2478_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2495_ = v_b_2478_;
v_isShared_2496_ = v_isSharedCheck_2523_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_snd_2493_);
lean_inc(v_fst_2492_);
lean_dec(v_b_2478_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2523_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = l_Lean_instInhabitedExpr;
v___x_2498_ = lean_array_get_borrowed(v___x_2497_, v_fst_2492_, v_a_2477_);
lean_inc(v___x_2498_);
v___x_2499_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2498_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v_a_2502_; uint8_t v___x_2506_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref(v___x_2499_);
v___x_2506_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2498_, v_a_2500_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_dec(v_snd_2493_);
v___x_2507_ = lean_array_set(v_fst_2492_, v_a_2477_, v_a_2500_);
v___x_2508_ = lean_box(v___x_2476_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v___x_2508_);
lean_ctor_set(v___x_2495_, 0, v___x_2507_);
v___x_2510_ = v___x_2495_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
v_a_2502_ = v___x_2510_;
goto v___jp_2501_;
}
}
else
{
lean_object* v___x_2513_; 
lean_dec(v_a_2500_);
if (v_isShared_2496_ == 0)
{
v___x_2513_ = v___x_2495_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_fst_2492_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_snd_2493_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
v_a_2502_ = v___x_2513_;
goto v___jp_2501_;
}
}
v___jp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_nat_add(v_a_2477_, v___x_2503_);
lean_dec(v_a_2477_);
v_a_2477_ = v___x_2504_;
v_b_2478_ = v_a_2502_;
goto _start;
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2495_);
lean_dec(v_snd_2493_);
lean_dec(v_fst_2492_);
lean_dec(v_a_2477_);
v_a_2515_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2499_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2499_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2524_, lean_object* v___x_2525_, lean_object* v_a_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v___x_15840__boxed_2539_; lean_object* v_res_2540_; 
v___x_15840__boxed_2539_ = lean_unbox(v___x_2525_);
v_res_2540_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2524_, v___x_15840__boxed_2539_, v_a_2526_, v_b_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec(v_upperBound_2524_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec(v_a_2542_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2554_, uint8_t v___x_2555_, lean_object* v_inst_2556_, lean_object* v_R_2557_, lean_object* v_a_2558_, lean_object* v_b_2559_, lean_object* v_c_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2554_, v___x_2555_, v_a_2558_, v_b_2559_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2573_ = _args[0];
lean_object* v___x_2574_ = _args[1];
lean_object* v_inst_2575_ = _args[2];
lean_object* v_R_2576_ = _args[3];
lean_object* v_a_2577_ = _args[4];
lean_object* v_b_2578_ = _args[5];
lean_object* v_c_2579_ = _args[6];
lean_object* v___y_2580_ = _args[7];
lean_object* v___y_2581_ = _args[8];
lean_object* v___y_2582_ = _args[9];
lean_object* v___y_2583_ = _args[10];
lean_object* v___y_2584_ = _args[11];
lean_object* v___y_2585_ = _args[12];
lean_object* v___y_2586_ = _args[13];
lean_object* v___y_2587_ = _args[14];
lean_object* v___y_2588_ = _args[15];
lean_object* v___y_2589_ = _args[16];
lean_object* v___y_2590_ = _args[17];
_start:
{
uint8_t v___x_16081__boxed_2591_; lean_object* v_res_2592_; 
v___x_16081__boxed_2591_ = lean_unbox(v___x_2574_);
v_res_2592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2573_, v___x_16081__boxed_2591_, v_inst_2575_, v_R_2576_, v_a_2577_, v_b_2578_, v_c_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec(v_upperBound_2573_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object* v_e_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_Expr_hasMVar(v_e_2593_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_e_2593_);
return v___x_2597_;
}
else
{
lean_object* v___x_2598_; lean_object* v_mctx_2599_; lean_object* v___x_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2603_; lean_object* v_cache_2604_; lean_object* v_zetaDeltaFVarIds_2605_; lean_object* v_postponed_2606_; lean_object* v_diag_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2616_; 
v___x_2598_ = lean_st_ref_get(v___y_2594_);
v_mctx_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_ref(v_mctx_2599_);
lean_dec(v___x_2598_);
v___x_2600_ = l_Lean_instantiateMVarsCore(v_mctx_2599_, v_e_2593_);
v_fst_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_fst_2601_);
v_snd_2602_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_snd_2602_);
lean_dec_ref(v___x_2600_);
v___x_2603_ = lean_st_ref_take(v___y_2594_);
v_cache_2604_ = lean_ctor_get(v___x_2603_, 1);
v_zetaDeltaFVarIds_2605_ = lean_ctor_get(v___x_2603_, 2);
v_postponed_2606_ = lean_ctor_get(v___x_2603_, 3);
v_diag_2607_ = lean_ctor_get(v___x_2603_, 4);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v___x_2603_, 0);
lean_dec(v_unused_2617_);
v___x_2609_ = v___x_2603_;
v_isShared_2610_ = v_isSharedCheck_2616_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_diag_2607_);
lean_inc(v_postponed_2606_);
lean_inc(v_zetaDeltaFVarIds_2605_);
lean_inc(v_cache_2604_);
lean_dec(v___x_2603_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2616_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_snd_2602_);
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_snd_2602_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_cache_2604_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_zetaDeltaFVarIds_2605_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_postponed_2606_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_diag_2607_);
v___x_2612_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_st_ref_set(v___y_2594_, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_fst_2601_);
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object* v_e_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2618_, v___y_2619_);
lean_dec(v___y_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_e_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2622_, v___y_2630_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_e_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_e_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(lean_object* v_k_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2650_);
lean_inc(v___y_2649_);
v___x_2660_ = lean_apply_11(v_k_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, lean_box(0));
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed(lean_object* v_k_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(v_k_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec(v___y_2662_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(lean_object* v_k_2674_, uint8_t v_allowLevelAssignments_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; 
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
lean_inc(v___y_2677_);
lean_inc(v___y_2676_);
v___f_2687_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2687_, 0, v_k_2674_);
lean_closure_set(v___f_2687_, 1, v___y_2676_);
lean_closure_set(v___f_2687_, 2, v___y_2677_);
lean_closure_set(v___f_2687_, 3, v___y_2678_);
lean_closure_set(v___f_2687_, 4, v___y_2679_);
lean_closure_set(v___f_2687_, 5, v___y_2680_);
lean_closure_set(v___f_2687_, 6, v___y_2681_);
v___x_2688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2675_, v___f_2687_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2688_) == 0)
{
return v___x_2688_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___boxed(lean_object* v_k_2697_, lean_object* v_allowLevelAssignments_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2710_; lean_object* v_res_2711_; 
v_allowLevelAssignments_boxed_2710_ = lean_unbox(v_allowLevelAssignments_2698_);
v_res_2711_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v_k_2697_, v_allowLevelAssignments_boxed_2710_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
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
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(lean_object* v_00_u03b1_2712_, lean_object* v_k_2713_, uint8_t v_allowLevelAssignments_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v_k_2713_, v_allowLevelAssignments_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_k_2728_, lean_object* v_allowLevelAssignments_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2741_; lean_object* v_res_2742_; 
v_allowLevelAssignments_boxed_2741_ = lean_unbox(v_allowLevelAssignments_2729_);
v_res_2742_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(v_00_u03b1_2727_, v_k_2728_, v_allowLevelAssignments_boxed_2741_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(lean_object* v_mvarId_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; lean_object* v_mctx_2747_; lean_object* v_decl_2748_; lean_object* v_depth_2749_; lean_object* v_depth_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2746_ = lean_st_ref_get(v___y_2744_);
v_mctx_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc_ref(v_mctx_2747_);
lean_dec(v___x_2746_);
lean_inc_ref(v_mctx_2747_);
v_decl_2748_ = l_Lean_MetavarContext_getDecl(v_mctx_2747_, v_mvarId_2743_);
v_depth_2749_ = lean_ctor_get(v_decl_2748_, 3);
lean_inc(v_depth_2749_);
lean_dec_ref(v_decl_2748_);
v_depth_2750_ = lean_ctor_get(v_mctx_2747_, 0);
lean_inc(v_depth_2750_);
lean_dec_ref(v_mctx_2747_);
v___x_2751_ = lean_nat_dec_eq(v_depth_2749_, v_depth_2750_);
lean_dec(v_depth_2750_);
lean_dec(v_depth_2749_);
v___x_2752_ = lean_box(v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg___boxed(lean_object* v_mvarId_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_2754_, v___y_2755_);
lean_dec(v___y_2755_);
return v_res_2757_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_instMonadEIO(lean_box(0));
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(lean_object* v_msg_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_toApplicative_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2845_; 
v___x_2775_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0);
v___x_2776_ = l_StateRefT_x27_instMonad___redArg(v___x_2775_);
v_toApplicative_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2776_, 1);
lean_dec(v_unused_2846_);
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2845_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_toApplicative_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2845_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_toFunctor_2781_; lean_object* v_toSeq_2782_; lean_object* v_toSeqLeft_2783_; lean_object* v_toSeqRight_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2843_; 
v_toFunctor_2781_ = lean_ctor_get(v_toApplicative_2777_, 0);
v_toSeq_2782_ = lean_ctor_get(v_toApplicative_2777_, 2);
v_toSeqLeft_2783_ = lean_ctor_get(v_toApplicative_2777_, 3);
v_toSeqRight_2784_ = lean_ctor_get(v_toApplicative_2777_, 4);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_toApplicative_2777_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v_toApplicative_2777_, 1);
lean_dec(v_unused_2844_);
v___x_2786_ = v_toApplicative_2777_;
v_isShared_2787_ = v_isSharedCheck_2843_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_toSeqRight_2784_);
lean_inc(v_toSeqLeft_2783_);
lean_inc(v_toSeq_2782_);
lean_inc(v_toFunctor_2781_);
lean_dec(v_toApplicative_2777_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2843_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___f_2793_; lean_object* v___f_2794_; lean_object* v___f_2795_; lean_object* v___x_2797_; 
v___f_2788_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__1));
v___f_2789_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__2));
lean_inc_ref(v_toFunctor_2781_);
v___f_2790_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2790_, 0, v_toFunctor_2781_);
v___f_2791_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2791_, 0, v_toFunctor_2781_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___f_2790_);
lean_ctor_set(v___x_2792_, 1, v___f_2791_);
v___f_2793_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2793_, 0, v_toSeqRight_2784_);
v___f_2794_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2794_, 0, v_toSeqLeft_2783_);
v___f_2795_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2795_, 0, v_toSeq_2782_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 4, v___f_2793_);
lean_ctor_set(v___x_2786_, 3, v___f_2794_);
lean_ctor_set(v___x_2786_, 2, v___f_2795_);
lean_ctor_set(v___x_2786_, 1, v___f_2788_);
lean_ctor_set(v___x_2786_, 0, v___x_2792_);
v___x_2797_ = v___x_2786_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___f_2788_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v___f_2795_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v___f_2794_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v___f_2793_);
v___x_2797_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2799_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v___f_2789_);
lean_ctor_set(v___x_2779_, 0, v___x_2797_);
v___x_2799_ = v___x_2779_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___f_2789_);
v___x_2799_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; lean_object* v_toApplicative_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2839_; 
v___x_2800_ = l_StateRefT_x27_instMonad___redArg(v___x_2799_);
v_toApplicative_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2800_, 1);
lean_dec(v_unused_2840_);
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2839_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_toApplicative_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2839_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v_toFunctor_2805_; lean_object* v_toSeq_2806_; lean_object* v_toSeqLeft_2807_; lean_object* v_toSeqRight_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2837_; 
v_toFunctor_2805_ = lean_ctor_get(v_toApplicative_2801_, 0);
v_toSeq_2806_ = lean_ctor_get(v_toApplicative_2801_, 2);
v_toSeqLeft_2807_ = lean_ctor_get(v_toApplicative_2801_, 3);
v_toSeqRight_2808_ = lean_ctor_get(v_toApplicative_2801_, 4);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_toApplicative_2801_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v_toApplicative_2801_, 1);
lean_dec(v_unused_2838_);
v___x_2810_ = v_toApplicative_2801_;
v_isShared_2811_ = v_isSharedCheck_2837_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_toSeqRight_2808_);
lean_inc(v_toSeqLeft_2807_);
lean_inc(v_toSeq_2806_);
lean_inc(v_toFunctor_2805_);
lean_dec(v_toApplicative_2801_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2837_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___f_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; lean_object* v___f_2818_; lean_object* v___f_2819_; lean_object* v___x_2821_; 
v___f_2812_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__3));
v___f_2813_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__4));
lean_inc_ref(v_toFunctor_2805_);
v___f_2814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2814_, 0, v_toFunctor_2805_);
v___f_2815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2815_, 0, v_toFunctor_2805_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___f_2814_);
lean_ctor_set(v___x_2816_, 1, v___f_2815_);
v___f_2817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2817_, 0, v_toSeqRight_2808_);
v___f_2818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2818_, 0, v_toSeqLeft_2807_);
v___f_2819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2819_, 0, v_toSeq_2806_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 4, v___f_2817_);
lean_ctor_set(v___x_2810_, 3, v___f_2818_);
lean_ctor_set(v___x_2810_, 2, v___f_2819_);
lean_ctor_set(v___x_2810_, 1, v___f_2812_);
lean_ctor_set(v___x_2810_, 0, v___x_2816_);
v___x_2821_ = v___x_2810_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___f_2812_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v___f_2819_);
lean_ctor_set(v_reuseFailAlloc_2836_, 3, v___f_2818_);
lean_ctor_set(v_reuseFailAlloc_2836_, 4, v___f_2817_);
v___x_2821_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 1, v___f_2813_);
lean_ctor_set(v___x_2803_, 0, v___x_2821_);
v___x_2823_ = v___x_2803_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___f_2813_);
v___x_2823_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_100179__overap_2833_; lean_object* v___x_2834_; 
v___x_2824_ = l_StateRefT_x27_instMonad___redArg(v___x_2823_);
v___x_2825_ = l_ReaderT_instMonad___redArg(v___x_2824_);
v___x_2826_ = l_StateRefT_x27_instMonad___redArg(v___x_2825_);
v___x_2827_ = l_ReaderT_instMonad___redArg(v___x_2826_);
v___x_2828_ = l_ReaderT_instMonad___redArg(v___x_2827_);
v___x_2829_ = l_StateRefT_x27_instMonad___redArg(v___x_2828_);
v___x_2830_ = 0;
v___x_2831_ = lean_box(v___x_2830_);
v___x_2832_ = l_instInhabitedOfMonad___redArg(v___x_2829_, v___x_2831_);
v___x_100179__overap_2833_ = lean_panic_fn(v___x_2832_, v_msg_2763_);
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
lean_inc(v___y_2771_);
lean_inc_ref(v___y_2770_);
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v___y_2767_);
lean_inc_ref(v___y_2766_);
lean_inc(v___y_2765_);
lean_inc(v___y_2764_);
v___x_2834_ = lean_apply_11(v___x_100179__overap_2833_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, lean_box(0));
return v___x_2834_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_msg_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(v_msg_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_keys_2860_, lean_object* v_vals_2861_, lean_object* v_i_2862_, lean_object* v_k_2863_){
_start:
{
lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = lean_array_get_size(v_keys_2860_);
v___x_2865_ = lean_nat_dec_lt(v_i_2862_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v_i_2862_);
v___x_2866_ = lean_box(0);
return v___x_2866_;
}
else
{
lean_object* v_k_x27_2867_; uint8_t v___x_2868_; 
v_k_x27_2867_ = lean_array_fget_borrowed(v_keys_2860_, v_i_2862_);
v___x_2868_ = l_Lean_instBEqLevelMVarId_beq(v_k_2863_, v_k_x27_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = lean_nat_add(v_i_2862_, v___x_2869_);
lean_dec(v_i_2862_);
v_i_2862_ = v___x_2870_;
goto _start;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_array_fget_borrowed(v_vals_2861_, v_i_2862_);
lean_dec(v_i_2862_);
lean_inc(v___x_2872_);
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_keys_2874_, lean_object* v_vals_2875_, lean_object* v_i_2876_, lean_object* v_k_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_keys_2874_, v_vals_2875_, v_i_2876_, v_k_2877_);
lean_dec(v_k_2877_);
lean_dec_ref(v_vals_2875_);
lean_dec_ref(v_keys_2874_);
return v_res_2878_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_2879_; size_t v___x_2880_; size_t v___x_2881_; 
v___x_2879_ = ((size_t)5ULL);
v___x_2880_ = ((size_t)1ULL);
v___x_2881_ = lean_usize_shift_left(v___x_2880_, v___x_2879_);
return v___x_2881_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_2882_; size_t v___x_2883_; size_t v___x_2884_; 
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_2884_ = lean_usize_sub(v___x_2883_, v___x_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(lean_object* v_x_2885_, size_t v_x_2886_, lean_object* v_x_2887_){
_start:
{
if (lean_obj_tag(v_x_2885_) == 0)
{
lean_object* v_es_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2909_; 
v_es_2888_ = lean_ctor_get(v_x_2885_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_x_2885_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2890_ = v_x_2885_;
v_isShared_2891_ = v_isSharedCheck_2909_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_es_2888_);
lean_dec(v_x_2885_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2909_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v_j_2896_; lean_object* v___x_2897_; 
v___x_2892_ = lean_box(2);
v___x_2893_ = ((size_t)5ULL);
v___x_2894_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_2895_ = lean_usize_land(v_x_2886_, v___x_2894_);
v_j_2896_ = lean_usize_to_nat(v___x_2895_);
v___x_2897_ = lean_array_get(v___x_2892_, v_es_2888_, v_j_2896_);
lean_dec(v_j_2896_);
lean_dec_ref(v_es_2888_);
switch(lean_obj_tag(v___x_2897_))
{
case 0:
{
lean_object* v_key_2898_; lean_object* v_val_2899_; uint8_t v___x_2900_; 
v_key_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_key_2898_);
v_val_2899_ = lean_ctor_get(v___x_2897_, 1);
lean_inc(v_val_2899_);
lean_dec_ref(v___x_2897_);
v___x_2900_ = l_Lean_instBEqLevelMVarId_beq(v_x_2887_, v_key_2898_);
lean_dec(v_key_2898_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; 
lean_dec(v_val_2899_);
lean_del_object(v___x_2890_);
v___x_2901_ = lean_box(0);
return v___x_2901_;
}
else
{
lean_object* v___x_2903_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 1);
lean_ctor_set(v___x_2890_, 0, v_val_2899_);
v___x_2903_ = v___x_2890_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_val_2899_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
case 1:
{
lean_object* v_node_2905_; size_t v___x_2906_; 
lean_del_object(v___x_2890_);
v_node_2905_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_node_2905_);
lean_dec_ref(v___x_2897_);
v___x_2906_ = lean_usize_shift_right(v_x_2886_, v___x_2893_);
v_x_2885_ = v_node_2905_;
v_x_2886_ = v___x_2906_;
goto _start;
}
default: 
{
lean_object* v___x_2908_; 
lean_del_object(v___x_2890_);
v___x_2908_ = lean_box(0);
return v___x_2908_;
}
}
}
}
else
{
lean_object* v_ks_2910_; lean_object* v_vs_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_ks_2910_ = lean_ctor_get(v_x_2885_, 0);
lean_inc_ref(v_ks_2910_);
v_vs_2911_ = lean_ctor_get(v_x_2885_, 1);
lean_inc_ref(v_vs_2911_);
lean_dec_ref(v_x_2885_);
v___x_2912_ = lean_unsigned_to_nat(0u);
v___x_2913_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_ks_2910_, v_vs_2911_, v___x_2912_, v_x_2887_);
lean_dec_ref(v_vs_2911_);
lean_dec_ref(v_ks_2910_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_){
_start:
{
size_t v_x_100960__boxed_2917_; lean_object* v_res_2918_; 
v_x_100960__boxed_2917_ = lean_unbox_usize(v_x_2915_);
lean_dec(v_x_2915_);
v_res_2918_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_2914_, v_x_100960__boxed_2917_, v_x_2916_);
lean_dec(v_x_2916_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_2919_, lean_object* v_x_2920_){
_start:
{
uint64_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v___x_2921_ = l_Lean_instHashableLevelMVarId_hash(v_x_2920_);
v___x_2922_ = lean_uint64_to_usize(v___x_2921_);
v___x_2923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_2919_, v___x_2922_, v_x_2920_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_x_2924_, lean_object* v_x_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_x_2924_, v_x_2925_);
lean_dec(v_x_2925_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(lean_object* v_mvarId_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; lean_object* v_mctx_2943_; lean_object* v_levelAssignDepth_2944_; lean_object* v_lDepth_2945_; lean_object* v___x_2946_; 
v___x_2942_ = lean_st_ref_get(v___y_2938_);
v_mctx_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_ref(v_mctx_2943_);
lean_dec(v___x_2942_);
v_levelAssignDepth_2944_ = lean_ctor_get(v_mctx_2943_, 1);
lean_inc(v_levelAssignDepth_2944_);
v_lDepth_2945_ = lean_ctor_get(v_mctx_2943_, 3);
lean_inc_ref(v_lDepth_2945_);
lean_dec_ref(v_mctx_2943_);
v___x_2946_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_lDepth_2945_, v_mvarId_2930_);
if (lean_obj_tag(v___x_2946_) == 1)
{
lean_object* v_val_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_mvarId_2930_);
v_val_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2956_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_val_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2956_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = lean_nat_dec_le(v_levelAssignDepth_2944_, v_val_2947_);
lean_dec(v_val_2947_);
lean_dec(v_levelAssignDepth_2944_);
v___x_2952_ = lean_box(v___x_2951_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2952_);
v___x_2954_ = v___x_2949_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_dec(v___x_2946_);
lean_dec(v_levelAssignDepth_2944_);
v___x_2957_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__0));
v___x_2958_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__1));
v___x_2959_ = lean_unsigned_to_nat(451u);
v___x_2960_ = lean_unsigned_to_nat(14u);
v___x_2961_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__2));
v___x_2962_ = 1;
v___x_2963_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2930_, v___x_2962_);
v___x_2964_ = lean_string_append(v___x_2961_, v___x_2963_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_mkPanicMessageWithDecl(v___x_2957_, v___x_2958_, v___x_2959_, v___x_2960_, v___x_2964_);
lean_dec_ref(v___x_2964_);
v___x_2966_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(v___x_2965_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___boxed(lean_object* v_mvarId_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(v_mvarId_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec(v___y_2968_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object* v_x_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___y_2993_; lean_object* v___y_2994_; uint8_t v_a_2995_; lean_object* v_lvl_u2081_3001_; lean_object* v_lvl_u2082_3002_; 
switch(lean_obj_tag(v_x_2980_))
{
case 1:
{
lean_object* v_a_3009_; uint8_t v___x_3010_; 
v_a_3009_ = lean_ctor_get(v_x_2980_, 0);
lean_inc(v_a_3009_);
lean_dec_ref(v_x_2980_);
v___x_3010_ = l_Lean_Level_hasMVar(v_a_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v_a_3009_);
v___x_3011_ = lean_box(v___x_3010_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
else
{
v_x_2980_ = v_a_3009_;
goto _start;
}
}
case 2:
{
lean_object* v_a_3014_; lean_object* v_a_3015_; 
v_a_3014_ = lean_ctor_get(v_x_2980_, 0);
lean_inc(v_a_3014_);
v_a_3015_ = lean_ctor_get(v_x_2980_, 1);
lean_inc(v_a_3015_);
lean_dec_ref(v_x_2980_);
v_lvl_u2081_3001_ = v_a_3014_;
v_lvl_u2082_3002_ = v_a_3015_;
goto v___jp_3000_;
}
case 3:
{
lean_object* v_a_3016_; lean_object* v_a_3017_; 
v_a_3016_ = lean_ctor_get(v_x_2980_, 0);
lean_inc(v_a_3016_);
v_a_3017_ = lean_ctor_get(v_x_2980_, 1);
lean_inc(v_a_3017_);
lean_dec_ref(v_x_2980_);
v_lvl_u2081_3001_ = v_a_3016_;
v_lvl_u2082_3002_ = v_a_3017_;
goto v___jp_3000_;
}
case 5:
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v_x_2980_, 0);
lean_inc(v_a_3018_);
lean_dec_ref(v_x_2980_);
v___x_3019_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(v_a_3018_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3019_;
}
default: 
{
uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec(v_x_2980_);
v___x_3020_ = 0;
v___x_3021_ = lean_box(v___x_3020_);
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
return v___x_3022_;
}
}
v___jp_2992_:
{
if (v_a_2995_ == 0)
{
uint8_t v___x_2996_; 
lean_dec_ref(v___y_2994_);
v___x_2996_ = l_Lean_Level_hasMVar(v___y_2993_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v___y_2993_);
v___x_2997_ = lean_box(v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
else
{
v_x_2980_ = v___y_2993_;
goto _start;
}
}
else
{
lean_dec(v___y_2993_);
return v___y_2994_;
}
}
v___jp_3000_:
{
uint8_t v___x_3003_; 
v___x_3003_ = l_Lean_Level_hasMVar(v_lvl_u2081_3001_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v_lvl_u2081_3001_);
v___x_3004_ = lean_box(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
v___y_2993_ = v_lvl_u2082_3002_;
v___y_2994_ = v___x_3005_;
v_a_2995_ = v___x_3003_;
goto v___jp_2992_;
}
else
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_lvl_u2081_3001_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; uint8_t v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
v___x_3008_ = lean_unbox(v_a_3007_);
lean_dec(v_a_3007_);
v___y_2993_ = v_lvl_u2082_3002_;
v___y_2994_ = v___x_3006_;
v_a_2995_ = v___x_3008_;
goto v___jp_2992_;
}
else
{
lean_dec(v_lvl_u2082_3002_);
return v___x_3006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object* v_x_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_x_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(lean_object* v_x_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
if (lean_obj_tag(v_x_3036_) == 0)
{
uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = 0;
v___x_3049_ = lean_box(v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v_head_3051_; lean_object* v_tail_3052_; lean_object* v___x_3053_; 
v_head_3051_ = lean_ctor_get(v_x_3036_, 0);
lean_inc(v_head_3051_);
v_tail_3052_ = lean_ctor_get(v_x_3036_, 1);
lean_inc(v_tail_3052_);
lean_dec_ref(v_x_3036_);
v___x_3053_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_head_3051_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; uint8_t v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
v___x_3055_ = lean_unbox(v_a_3054_);
lean_dec(v_a_3054_);
if (v___x_3055_ == 0)
{
lean_dec_ref(v___x_3053_);
v_x_3036_ = v_tail_3052_;
goto _start;
}
else
{
lean_dec(v_tail_3052_);
return v___x_3053_;
}
}
else
{
lean_dec(v_tail_3052_);
return v___x_3053_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4___boxed(lean_object* v_x_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(v_x_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec(v___y_3058_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_x_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___y_3083_; lean_object* v___y_3084_; uint8_t v_a_3085_; lean_object* v_d_3091_; lean_object* v_b_3092_; 
switch(lean_obj_tag(v_x_3070_))
{
case 2:
{
lean_object* v_mvarId_3099_; lean_object* v___x_3100_; 
v_mvarId_3099_ = lean_ctor_get(v_x_3070_, 0);
lean_inc(v_mvarId_3099_);
lean_dec_ref(v_x_3070_);
v___x_3100_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_3099_, v___y_3078_);
return v___x_3100_;
}
case 3:
{
lean_object* v_u_3101_; lean_object* v___x_3102_; 
v_u_3101_ = lean_ctor_get(v_x_3070_, 0);
lean_inc(v_u_3101_);
lean_dec_ref(v_x_3070_);
v___x_3102_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_u_3101_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
return v___x_3102_;
}
case 4:
{
lean_object* v_us_3103_; lean_object* v___x_3104_; 
v_us_3103_ = lean_ctor_get(v_x_3070_, 1);
lean_inc(v_us_3103_);
lean_dec_ref(v_x_3070_);
v___x_3104_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(v_us_3103_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
return v___x_3104_;
}
case 5:
{
lean_object* v_fn_3105_; lean_object* v_arg_3106_; lean_object* v___y_3108_; uint8_t v_a_3109_; uint8_t v___x_3114_; 
v_fn_3105_ = lean_ctor_get(v_x_3070_, 0);
lean_inc_ref(v_fn_3105_);
v_arg_3106_ = lean_ctor_get(v_x_3070_, 1);
lean_inc_ref(v_arg_3106_);
lean_dec_ref(v_x_3070_);
v___x_3114_ = l_Lean_Expr_hasMVar(v_fn_3105_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec_ref(v_fn_3105_);
v___x_3115_ = lean_box(v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
v___y_3108_ = v___x_3116_;
v_a_3109_ = v___x_3114_;
goto v___jp_3107_;
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_fn_3105_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; uint8_t v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
v___x_3119_ = lean_unbox(v_a_3118_);
lean_dec(v_a_3118_);
v___y_3108_ = v___x_3117_;
v_a_3109_ = v___x_3119_;
goto v___jp_3107_;
}
else
{
lean_dec_ref(v_arg_3106_);
return v___x_3117_;
}
}
v___jp_3107_:
{
if (v_a_3109_ == 0)
{
uint8_t v___x_3110_; 
lean_dec_ref(v___y_3108_);
v___x_3110_ = l_Lean_Expr_hasMVar(v_arg_3106_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec_ref(v_arg_3106_);
v___x_3111_ = lean_box(v___x_3110_);
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
else
{
v_x_3070_ = v_arg_3106_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_3106_);
return v___y_3108_;
}
}
}
case 6:
{
lean_object* v_binderType_3120_; lean_object* v_body_3121_; 
v_binderType_3120_ = lean_ctor_get(v_x_3070_, 1);
lean_inc_ref(v_binderType_3120_);
v_body_3121_ = lean_ctor_get(v_x_3070_, 2);
lean_inc_ref(v_body_3121_);
lean_dec_ref(v_x_3070_);
v_d_3091_ = v_binderType_3120_;
v_b_3092_ = v_body_3121_;
goto v___jp_3090_;
}
case 7:
{
lean_object* v_binderType_3122_; lean_object* v_body_3123_; 
v_binderType_3122_ = lean_ctor_get(v_x_3070_, 1);
lean_inc_ref(v_binderType_3122_);
v_body_3123_ = lean_ctor_get(v_x_3070_, 2);
lean_inc_ref(v_body_3123_);
lean_dec_ref(v_x_3070_);
v_d_3091_ = v_binderType_3122_;
v_b_3092_ = v_body_3123_;
goto v___jp_3090_;
}
case 8:
{
lean_object* v_type_3124_; lean_object* v_value_3125_; lean_object* v_body_3126_; lean_object* v___y_3128_; uint8_t v_a_3129_; lean_object* v___y_3135_; uint8_t v_a_3136_; uint8_t v___x_3143_; 
v_type_3124_ = lean_ctor_get(v_x_3070_, 1);
lean_inc_ref(v_type_3124_);
v_value_3125_ = lean_ctor_get(v_x_3070_, 2);
lean_inc_ref(v_value_3125_);
v_body_3126_ = lean_ctor_get(v_x_3070_, 3);
lean_inc_ref(v_body_3126_);
lean_dec_ref(v_x_3070_);
v___x_3143_ = l_Lean_Expr_hasMVar(v_type_3124_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_dec_ref(v_type_3124_);
v___x_3144_ = lean_box(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
v___y_3135_ = v___x_3145_;
v_a_3136_ = v___x_3143_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_type_3124_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; uint8_t v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
v___x_3148_ = lean_unbox(v_a_3147_);
lean_dec(v_a_3147_);
v___y_3135_ = v___x_3146_;
v_a_3136_ = v___x_3148_;
goto v___jp_3134_;
}
else
{
lean_dec_ref(v_body_3126_);
lean_dec_ref(v_value_3125_);
return v___x_3146_;
}
}
v___jp_3127_:
{
if (v_a_3129_ == 0)
{
uint8_t v___x_3130_; 
lean_dec_ref(v___y_3128_);
v___x_3130_ = l_Lean_Expr_hasMVar(v_body_3126_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec_ref(v_body_3126_);
v___x_3131_ = lean_box(v___x_3130_);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
else
{
v_x_3070_ = v_body_3126_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_3126_);
return v___y_3128_;
}
}
v___jp_3134_:
{
if (v_a_3136_ == 0)
{
uint8_t v___x_3137_; 
lean_dec_ref(v___y_3135_);
v___x_3137_ = l_Lean_Expr_hasMVar(v_value_3125_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec_ref(v_value_3125_);
v___x_3138_ = lean_box(v___x_3137_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
v___y_3128_ = v___x_3139_;
v_a_3129_ = v___x_3137_;
goto v___jp_3127_;
}
else
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_value_3125_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; uint8_t v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
v___x_3142_ = lean_unbox(v_a_3141_);
lean_dec(v_a_3141_);
v___y_3128_ = v___x_3140_;
v_a_3129_ = v___x_3142_;
goto v___jp_3127_;
}
else
{
lean_dec_ref(v_body_3126_);
return v___x_3140_;
}
}
}
else
{
lean_dec_ref(v_body_3126_);
lean_dec_ref(v_value_3125_);
return v___y_3135_;
}
}
}
case 10:
{
lean_object* v_expr_3149_; uint8_t v___x_3150_; 
v_expr_3149_ = lean_ctor_get(v_x_3070_, 1);
lean_inc_ref(v_expr_3149_);
lean_dec_ref(v_x_3070_);
v___x_3150_ = l_Lean_Expr_hasMVar(v_expr_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec_ref(v_expr_3149_);
v___x_3151_ = lean_box(v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
else
{
v_x_3070_ = v_expr_3149_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_3154_; uint8_t v___x_3155_; 
v_struct_3154_ = lean_ctor_get(v_x_3070_, 2);
lean_inc_ref(v_struct_3154_);
lean_dec_ref(v_x_3070_);
v___x_3155_ = l_Lean_Expr_hasMVar(v_struct_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref(v_struct_3154_);
v___x_3156_ = lean_box(v___x_3155_);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
else
{
v_x_3070_ = v_struct_3154_;
goto _start;
}
}
default: 
{
uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec_ref(v_x_3070_);
v___x_3159_ = 0;
v___x_3160_ = lean_box(v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
v___jp_3082_:
{
if (v_a_3085_ == 0)
{
uint8_t v___x_3086_; 
lean_dec_ref(v___y_3084_);
v___x_3086_ = l_Lean_Expr_hasMVar(v___y_3083_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref(v___y_3083_);
v___x_3087_ = lean_box(v___x_3086_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
else
{
v_x_3070_ = v___y_3083_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_3083_);
return v___y_3084_;
}
}
v___jp_3090_:
{
uint8_t v___x_3093_; 
v___x_3093_ = l_Lean_Expr_hasMVar(v_d_3091_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec_ref(v_d_3091_);
v___x_3094_ = lean_box(v___x_3093_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
v___y_3083_ = v_b_3092_;
v___y_3084_ = v___x_3095_;
v_a_3085_ = v___x_3093_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_d_3091_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; uint8_t v___x_3098_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
v___x_3098_ = lean_unbox(v_a_3097_);
lean_dec(v_a_3097_);
v___y_3083_ = v_b_3092_;
v___y_3084_ = v___x_3096_;
v_a_3085_ = v___x_3098_;
goto v___jp_3082_;
}
else
{
lean_dec_ref(v_b_3092_);
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_x_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_x_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec(v___y_3163_);
return v_res_3174_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_as_3186_, size_t v_sz_3187_, size_t v_i_3188_, lean_object* v_b_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_a_3202_; uint8_t v___x_3206_; 
v___x_3206_ = lean_usize_dec_lt(v_i_3188_, v_sz_3187_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_b_3189_);
return v___x_3207_;
}
else
{
lean_object* v_snd_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3401_; 
v_snd_3208_ = lean_ctor_get(v_b_3189_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_b_3189_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v_b_3189_, 0);
lean_dec(v_unused_3402_);
v___x_3210_ = v_b_3189_;
v_isShared_3211_ = v_isSharedCheck_3401_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_snd_3208_);
lean_dec(v_b_3189_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3401_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_array_3212_; lean_object* v_start_3213_; lean_object* v_stop_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; 
v_array_3212_ = lean_ctor_get(v_snd_3208_, 0);
v_start_3213_ = lean_ctor_get(v_snd_3208_, 1);
v_stop_3214_ = lean_ctor_get(v_snd_3208_, 2);
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_nat_dec_lt(v_start_3213_, v_stop_3214_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3218_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3215_);
v___x_3218_ = v___x_3210_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_snd_3208_);
v___x_3218_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
else
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3397_; 
lean_inc(v_stop_3214_);
lean_inc(v_start_3213_);
lean_inc_ref(v_array_3212_);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_snd_3208_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; lean_object* v_unused_3399_; lean_object* v_unused_3400_; 
v_unused_3398_ = lean_ctor_get(v_snd_3208_, 2);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_snd_3208_, 1);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_snd_3208_, 0);
lean_dec(v_unused_3400_);
v___x_3222_ = v_snd_3208_;
v_isShared_3223_ = v_isSharedCheck_3397_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v_snd_3208_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3397_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3224_ = lean_array_fget(v_array_3212_, v_start_3213_);
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_nat_add(v_start_3213_, v___x_3225_);
lean_dec(v_start_3213_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v___x_3226_);
v___x_3228_ = v___x_3222_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_array_3212_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_stop_3214_);
v___x_3228_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_unbox(v___x_3224_);
lean_dec(v___x_3224_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3231_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3228_);
lean_ctor_set(v___x_3210_, 0, v___x_3215_);
v___x_3231_ = v___x_3210_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v___x_3228_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
v_a_3202_ = v___x_3231_;
goto v___jp_3201_;
}
}
else
{
lean_object* v_a_3233_; lean_object* v_____x_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___x_3271_; 
v_a_3233_ = lean_array_uget_borrowed(v_as_3186_, v_i_3188_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v_a_3233_);
v___x_3271_ = lean_infer_type(v_a_3233_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3387_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3387_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3387_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3272_);
if (lean_obj_tag(v___x_3276_) == 1)
{
lean_object* v_val_3277_; lean_object* v_snd_3278_; lean_object* v_fst_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3381_; 
lean_del_object(v___x_3274_);
v_val_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_val_3277_);
lean_dec_ref(v___x_3276_);
v_snd_3278_ = lean_ctor_get(v_val_3277_, 1);
v_fst_3279_ = lean_ctor_get(v_val_3277_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_val_3277_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3281_ = v_val_3277_;
v_isShared_3282_ = v_isSharedCheck_3381_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_snd_3278_);
lean_inc(v_fst_3279_);
lean_dec(v_val_3277_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3381_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_fst_3283_; lean_object* v_snd_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3380_; 
v_fst_3283_ = lean_ctor_get(v_snd_3278_, 0);
v_snd_3284_ = lean_ctor_get(v_snd_3278_, 1);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_snd_3278_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3286_ = v_snd_3278_;
v_isShared_3287_ = v_isSharedCheck_3380_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_snd_3284_);
lean_inc(v_fst_3283_);
lean_dec(v_snd_3278_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3380_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; 
lean_inc(v_fst_3283_);
v___x_3288_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3283_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_cls_3344_; lean_object* v___x_3345_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref(v___x_3288_);
v_cls_3344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_3345_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3344_, v___y_3198_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; uint8_t v___x_3347_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = lean_unbox(v_a_3346_);
lean_dec(v_a_3346_);
if (v___x_3347_ == 0)
{
lean_del_object(v___x_3281_);
v___y_3291_ = v___y_3190_;
v___y_3292_ = v___y_3191_;
v___y_3293_ = v___y_3192_;
v___y_3294_ = v___y_3193_;
v___y_3295_ = v___y_3194_;
v___y_3296_ = v___y_3195_;
v___y_3297_ = v___y_3196_;
v___y_3298_ = v___y_3197_;
v___y_3299_ = v___y_3198_;
v___y_3300_ = v___y_3199_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_inc(v_a_3289_);
v___x_3348_ = l_Lean_MessageData_ofExpr(v_a_3289_);
v___x_3349_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4);
if (v_isShared_3282_ == 0)
{
lean_ctor_set_tag(v___x_3281_, 7);
lean_ctor_set(v___x_3281_, 1, v___x_3349_);
lean_ctor_set(v___x_3281_, 0, v___x_3348_);
v___x_3351_ = v___x_3281_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_inc(v_snd_3284_);
v___x_3352_ = l_Lean_MessageData_ofExpr(v_snd_3284_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3351_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3344_, v___x_3353_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_dec_ref(v___x_3354_);
v___y_3291_ = v___y_3190_;
v___y_3292_ = v___y_3191_;
v___y_3293_ = v___y_3192_;
v___y_3294_ = v___y_3193_;
v___y_3295_ = v___y_3194_;
v___y_3296_ = v___y_3195_;
v___y_3297_ = v___y_3196_;
v___y_3298_ = v___y_3197_;
v___y_3299_ = v___y_3198_;
v___y_3300_ = v___y_3199_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec(v_a_3289_);
lean_del_object(v___x_3286_);
lean_dec(v_snd_3284_);
lean_dec(v_fst_3283_);
lean_dec(v_fst_3279_);
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
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
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec(v_a_3289_);
lean_del_object(v___x_3286_);
lean_dec(v_snd_3284_);
lean_dec(v_fst_3283_);
lean_del_object(v___x_3281_);
lean_dec(v_fst_3279_);
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3364_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3345_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3345_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
v___jp_3290_:
{
lean_object* v___x_3301_; 
lean_inc(v_a_3289_);
v___x_3301_ = l_Lean_Meta_isDefEqD(v_a_3289_, v_snd_3284_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3335_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3335_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3335_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
uint8_t v___x_3306_; 
v___x_3306_ = lean_unbox(v_a_3302_);
lean_dec(v_a_3302_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3309_; 
lean_dec(v_a_3289_);
lean_dec(v_fst_3283_);
lean_dec(v_fst_3279_);
lean_del_object(v___x_3210_);
v___x_3307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v___x_3228_);
lean_ctor_set(v___x_3286_, 0, v___x_3307_);
v___x_3309_ = v___x_3286_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3228_);
v___x_3309_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3311_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3309_);
v___x_3311_ = v___x_3304_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
else
{
lean_del_object(v___x_3304_);
lean_del_object(v___x_3286_);
if (lean_obj_tag(v_fst_3279_) == 0)
{
uint8_t v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = 0;
v___x_3315_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3283_, v_a_3289_, v___x_3314_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3315_);
v_____x_3235_ = v_a_3316_;
v___y_3236_ = v___y_3297_;
v___y_3237_ = v___y_3298_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___y_3300_;
goto v___jp_3234_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3317_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v___x_3325_; 
lean_dec_ref(v_fst_3279_);
v___x_3325_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3283_, v_a_3289_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref(v___x_3325_);
v_____x_3235_ = v_a_3326_;
v___y_3236_ = v___y_3297_;
v___y_3237_ = v___y_3298_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___y_3300_;
goto v___jp_3234_;
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3327_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3325_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3325_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v_a_3289_);
lean_del_object(v___x_3286_);
lean_dec(v_fst_3283_);
lean_dec(v_fst_3279_);
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3336_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3301_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3301_);
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
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_del_object(v___x_3286_);
lean_dec(v_snd_3284_);
lean_dec(v_fst_3283_);
lean_del_object(v___x_3281_);
lean_dec(v_fst_3279_);
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3372_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3288_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3288_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_dec(v___x_3276_);
lean_del_object(v___x_3210_);
v___x_3382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v___x_3228_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3383_);
v___x_3385_ = v___x_3274_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3388_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3271_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3271_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
v___jp_3234_:
{
if (lean_obj_tag(v_____x_3235_) == 1)
{
lean_object* v_val_3240_; lean_object* v___x_3241_; 
v_val_3240_ = lean_ctor_get(v_____x_3235_, 0);
lean_inc(v_val_3240_);
lean_dec_ref(v_____x_3235_);
lean_inc(v_a_3233_);
v___x_3241_ = l_Lean_Meta_isExprDefEq(v_a_3233_, v_val_3240_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3257_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3257_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3257_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_unbox(v_a_3242_);
lean_dec(v_a_3242_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3228_);
lean_ctor_set(v___x_3210_, 0, v___x_3247_);
v___x_3249_ = v___x_3210_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3228_);
v___x_3249_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3249_);
v___x_3251_ = v___x_3244_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
else
{
lean_object* v___x_3255_; 
lean_del_object(v___x_3244_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3228_);
lean_ctor_set(v___x_3210_, 0, v___x_3215_);
v___x_3255_ = v___x_3210_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3228_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
v_a_3202_ = v___x_3255_;
goto v___jp_3201_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___x_3228_);
lean_del_object(v___x_3210_);
v_a_3258_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3241_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3241_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_dec(v_____x_3235_);
v___x_3266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3228_);
lean_ctor_set(v___x_3210_, 0, v___x_3266_);
v___x_3268_ = v___x_3210_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v___x_3228_);
v___x_3268_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
}
}
}
}
}
}
}
}
v___jp_3201_:
{
size_t v___x_3203_; size_t v___x_3204_; 
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_add(v_i_3188_, v___x_3203_);
v_i_3188_ = v___x_3204_;
v_b_3189_ = v_a_3202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_as_3403_, lean_object* v_sz_3404_, lean_object* v_i_3405_, lean_object* v_b_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
size_t v_sz_boxed_3418_; size_t v_i_boxed_3419_; lean_object* v_res_3420_; 
v_sz_boxed_3418_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3419_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_as_3403_, v_sz_boxed_3418_, v_i_boxed_3419_, v_b_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v_as_3403_);
return v_res_3420_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_arg_3424_, uint8_t v___x_3425_, lean_object* v_e_3426_, lean_object* v_cls_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; 
lean_inc_ref(v_arg_3424_);
v___x_3439_ = l_Lean_Meta_forallMetaTelescope(v_arg_3424_, v___x_3425_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v_fst_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3549_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref(v___x_3439_);
v_fst_3441_ = lean_ctor_get(v_a_3440_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v_a_3440_, 1);
lean_dec(v_unused_3550_);
v___x_3443_ = v_a_3440_;
v_isShared_3444_ = v_isSharedCheck_3549_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_fst_3441_);
lean_dec(v_a_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3549_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3445_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3424_);
lean_dec_ref(v_arg_3424_);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_array_get_size(v___x_3445_);
v___x_3448_ = l_Array_toSubarray___redArg(v___x_3445_, v___x_3446_, v___x_3447_);
v___x_3449_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3448_);
lean_ctor_set(v___x_3443_, 0, v___x_3449_);
v___x_3451_ = v___x_3443_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3448_);
v___x_3451_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
size_t v_sz_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
v_sz_3452_ = lean_array_size(v_fst_3441_);
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_fst_3441_, v_sz_3452_, v___x_3453_, v___x_3451_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3539_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3539_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3539_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_fst_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3537_; 
v_fst_3459_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; 
v_unused_3538_ = lean_ctor_get(v_a_3455_, 1);
lean_dec(v_unused_3538_);
v___x_3461_ = v_a_3455_;
v_isShared_3462_ = v_isSharedCheck_3537_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_fst_3459_);
lean_dec(v_a_3455_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3537_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
if (lean_obj_tag(v_fst_3459_) == 0)
{
lean_object* v___x_3463_; 
lean_del_object(v___x_3457_);
lean_inc_ref(v_e_3426_);
v___x_3463_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3426_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3524_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3463_);
v___x_3465_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3426_, v_a_3464_);
v___x_3466_ = l_Lean_mkAppN(v___x_3465_, v_fst_3441_);
lean_dec(v_fst_3441_);
v___x_3467_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v___x_3466_, v___y_3435_);
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3524_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3524_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3477_; 
lean_inc(v_a_3468_);
v___x_3477_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_a_3468_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3515_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3515_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3515_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
uint8_t v___x_3482_; 
v___x_3482_ = lean_unbox(v_a_3478_);
lean_dec(v_a_3478_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; lean_object* v_a_3484_; uint8_t v___x_3485_; 
lean_del_object(v___x_3480_);
lean_inc(v_cls_3427_);
v___x_3483_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3427_, v___y_3436_);
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = lean_unbox(v_a_3484_);
lean_dec(v_a_3484_);
if (v___x_3485_ == 0)
{
lean_del_object(v___x_3461_);
lean_dec(v_cls_3427_);
goto v___jp_3472_;
}
else
{
lean_object* v___x_3486_; 
lean_inc(v___y_3437_);
lean_inc_ref(v___y_3436_);
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v_a_3468_);
v___x_3486_ = lean_infer_type(v_a_3468_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref(v___x_3486_);
lean_inc(v_a_3468_);
v___x_3488_ = l_Lean_MessageData_ofExpr(v_a_3468_);
v___x_3489_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1);
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 7);
lean_ctor_set(v___x_3461_, 1, v___x_3489_);
lean_ctor_set(v___x_3461_, 0, v___x_3488_);
v___x_3491_ = v___x_3461_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = l_Lean_MessageData_ofExpr(v_a_3487_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3427_, v___x_3493_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_dec_ref(v___x_3494_);
goto v___jp_3472_;
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_del_object(v___x_3470_);
lean_dec(v_a_3468_);
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_del_object(v___x_3470_);
lean_dec(v_a_3468_);
lean_del_object(v___x_3461_);
lean_dec(v_cls_3427_);
v_a_3504_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3486_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3486_);
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
else
{
lean_object* v___x_3513_; 
lean_del_object(v___x_3470_);
lean_dec(v_a_3468_);
lean_del_object(v___x_3461_);
lean_dec(v_cls_3427_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3449_);
v___x_3513_ = v___x_3480_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3449_);
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
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_3470_);
lean_dec(v_a_3468_);
lean_del_object(v___x_3461_);
lean_dec(v_cls_3427_);
v_a_3516_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3477_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3477_);
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
v___jp_3472_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_a_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3473_);
v___x_3475_ = v___x_3470_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_del_object(v___x_3461_);
lean_dec(v_fst_3441_);
lean_dec(v_cls_3427_);
lean_dec_ref(v_e_3426_);
v_a_3525_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3463_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3463_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_val_3533_; lean_object* v___x_3535_; 
lean_del_object(v___x_3461_);
lean_dec(v_fst_3441_);
lean_dec(v_cls_3427_);
lean_dec_ref(v_e_3426_);
v_val_3533_ = lean_ctor_get(v_fst_3459_, 0);
lean_inc(v_val_3533_);
lean_dec_ref(v_fst_3459_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v_val_3533_);
v___x_3535_ = v___x_3457_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_val_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_fst_3441_);
lean_dec(v_cls_3427_);
lean_dec_ref(v_e_3426_);
v_a_3540_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3454_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3454_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_cls_3427_);
lean_dec_ref(v_e_3426_);
lean_dec_ref(v_arg_3424_);
v_a_3551_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3439_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3439_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_arg_3559_, lean_object* v___x_3560_, lean_object* v_e_3561_, lean_object* v_cls_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
uint8_t v___x_101956__boxed_3574_; lean_object* v_res_3575_; 
v___x_101956__boxed_3574_ = lean_unbox(v___x_3560_);
v_res_3575_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_arg_3559_, v___x_101956__boxed_3574_, v_e_3561_, v_cls_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec(v___y_3563_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_cls_3591_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___x_3643_; lean_object* v_a_3644_; uint8_t v___x_3645_; 
v_cls_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_3643_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3591_, v_a_3585_);
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = lean_unbox(v_a_3644_);
lean_dec(v_a_3644_);
if (v___x_3645_ == 0)
{
v___y_3593_ = v_a_3577_;
v___y_3594_ = v_a_3578_;
v___y_3595_ = v_a_3579_;
v___y_3596_ = v_a_3580_;
v___y_3597_ = v_a_3581_;
v___y_3598_ = v_a_3582_;
v___y_3599_ = v_a_3583_;
v___y_3600_ = v_a_3584_;
v___y_3601_ = v_a_3585_;
v___y_3602_ = v_a_3586_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Meta_Grind_updateLastTag(v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec_ref(v___x_3646_);
lean_inc_ref(v_e_3576_);
v___x_3647_ = l_Lean_MessageData_ofExpr(v_e_3576_);
v___x_3648_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3591_, v___x_3647_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_dec_ref(v___x_3648_);
v___y_3593_ = v_a_3577_;
v___y_3594_ = v_a_3578_;
v___y_3595_ = v_a_3579_;
v___y_3596_ = v_a_3580_;
v___y_3597_ = v_a_3581_;
v___y_3598_ = v_a_3582_;
v___y_3599_ = v_a_3583_;
v___y_3600_ = v_a_3584_;
v___y_3601_ = v_a_3585_;
v___y_3602_ = v_a_3586_;
goto v___jp_3592_;
}
else
{
lean_dec_ref(v_e_3576_);
return v___x_3648_;
}
}
else
{
lean_dec_ref(v_e_3576_);
return v___x_3646_;
}
}
v___jp_3588_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_box(0);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
v___jp_3592_:
{
lean_object* v___x_3603_; 
lean_inc_ref(v_e_3576_);
v___x_3603_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3576_, v___y_3600_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
v___x_3605_ = l_Lean_Expr_cleanupAnnotations(v_a_3604_);
v___x_3606_ = l_Lean_Expr_isApp(v___x_3605_);
if (v___x_3606_ == 0)
{
lean_dec_ref(v___x_3605_);
lean_dec_ref(v_e_3576_);
goto v___jp_3588_;
}
else
{
lean_object* v_arg_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_arg_3607_ = lean_ctor_get(v___x_3605_, 1);
lean_inc_ref(v_arg_3607_);
v___x_3608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3605_);
v___x_3609_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3610_ = l_Lean_Expr_isConstOf(v___x_3608_, v___x_3609_);
lean_dec_ref(v___x_3608_);
if (v___x_3610_ == 0)
{
lean_dec_ref(v_arg_3607_);
lean_dec_ref(v_e_3576_);
goto v___jp_3588_;
}
else
{
uint8_t v___x_3611_; lean_object* v___x_3612_; lean_object* v___f_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; 
v___x_3611_ = 0;
v___x_3612_ = lean_box(v___x_3611_);
v___f_3613_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed), 15, 4);
lean_closure_set(v___f_3613_, 0, v_arg_3607_);
lean_closure_set(v___f_3613_, 1, v___x_3612_);
lean_closure_set(v___f_3613_, 2, v_e_3576_);
lean_closure_set(v___f_3613_, 3, v_cls_3591_);
v___x_3614_ = 0;
v___x_3615_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v___f_3613_, v___x_3614_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3626_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
if (lean_obj_tag(v_a_3616_) == 1)
{
lean_object* v_val_3620_; lean_object* v___x_3621_; 
lean_del_object(v___x_3618_);
v_val_3620_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_val_3620_);
lean_dec_ref(v_a_3616_);
v___x_3621_ = l_Lean_Meta_Grind_closeGoal(v_val_3620_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
return v___x_3621_;
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
lean_dec(v_a_3616_);
v___x_3622_ = lean_box(0);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3622_);
v___x_3624_ = v___x_3618_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
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
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
v_a_3627_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3615_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3615_);
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
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_e_3576_);
v_a_3635_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3603_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3603_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_a_3657_);
lean_dec_ref(v_a_3656_);
lean_dec(v_a_3655_);
lean_dec_ref(v_a_3654_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec(v_a_3651_);
lean_dec(v_a_3650_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(lean_object* v_mvarId_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_3662_, v___y_3670_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___boxed(lean_object* v_mvarId_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(v_mvarId_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec(v___y_3676_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_x_3689_, v_x_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(v_00_u03b2_3692_, v_x_3693_, v_x_3694_);
lean_dec(v_x_3694_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_3696_, lean_object* v_x_3697_, size_t v_x_3698_, lean_object* v_x_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_3697_, v_x_3698_, v_x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3701_, lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v_x_3704_){
_start:
{
size_t v_x_102438__boxed_3705_; lean_object* v_res_3706_; 
v_x_102438__boxed_3705_ = lean_unbox_usize(v_x_3703_);
lean_dec(v_x_3703_);
v_res_3706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(v_00_u03b2_3701_, v_x_3702_, v_x_102438__boxed_3705_, v_x_3704_);
lean_dec(v_x_3704_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_3707_, lean_object* v_keys_3708_, lean_object* v_vals_3709_, lean_object* v_heq_3710_, lean_object* v_i_3711_, lean_object* v_k_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_keys_3708_, v_vals_3709_, v_i_3711_, v_k_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_3714_, lean_object* v_keys_3715_, lean_object* v_vals_3716_, lean_object* v_heq_3717_, lean_object* v_i_3718_, lean_object* v_k_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_3714_, v_keys_3715_, v_vals_3716_, v_heq_3717_, v_i_3718_, v_k_3719_);
lean_dec(v_k_3719_);
lean_dec_ref(v_vals_3716_);
lean_dec_ref(v_keys_3715_);
return v_res_3720_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v_cls_3753_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___x_3857_; lean_object* v_a_3858_; uint8_t v___x_3859_; 
v_cls_3753_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_3857_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3753_, v_a_3736_);
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref(v___x_3857_);
v___x_3859_ = lean_unbox(v_a_3858_);
lean_dec(v_a_3858_);
if (v___x_3859_ == 0)
{
v___y_3755_ = v_a_3728_;
v___y_3756_ = v_a_3729_;
v___y_3757_ = v_a_3730_;
v___y_3758_ = v_a_3731_;
v___y_3759_ = v_a_3732_;
v___y_3760_ = v_a_3733_;
v___y_3761_ = v_a_3734_;
v___y_3762_ = v_a_3735_;
v___y_3763_ = v_a_3736_;
v___y_3764_ = v_a_3737_;
goto v___jp_3754_;
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_Meta_Grind_updateLastTag(v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec_ref(v___x_3860_);
v___x_3861_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3727_);
v___x_3862_ = l_Lean_indentExpr(v_e_3727_);
v___x_3863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3753_, v___x_3863_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_dec_ref(v___x_3864_);
v___y_3755_ = v_a_3728_;
v___y_3756_ = v_a_3729_;
v___y_3757_ = v_a_3730_;
v___y_3758_ = v_a_3731_;
v___y_3759_ = v_a_3732_;
v___y_3760_ = v_a_3733_;
v___y_3761_ = v_a_3734_;
v___y_3762_ = v_a_3735_;
v___y_3763_ = v_a_3736_;
v___y_3764_ = v_a_3737_;
goto v___jp_3754_;
}
else
{
lean_dec_ref(v_e_3727_);
return v___x_3864_;
}
}
else
{
lean_dec_ref(v_e_3727_);
return v___x_3860_;
}
}
v___jp_3739_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_box(0);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
return v___x_3741_;
}
v___jp_3742_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_inc_ref(v_e_3727_);
v___x_3751_ = l_Lean_Meta_mkEqTrueCore(v_e_3727_, v___y_3743_);
v___x_3752_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3727_, v___x_3751_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3752_;
}
v___jp_3754_:
{
lean_object* v___x_3765_; 
lean_inc_ref(v_e_3727_);
v___x_3765_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3727_, v___y_3755_, v___y_3759_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; uint8_t v___x_3767_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = lean_unbox(v_a_3766_);
lean_dec(v_a_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_inc_ref(v_e_3727_);
v___x_3768_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3727_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3820_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3820_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3820_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
uint8_t v___x_3773_; 
v___x_3773_ = lean_unbox(v_a_3769_);
lean_dec(v_a_3769_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec_ref(v_e_3727_);
v___x_3774_ = lean_box(0);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3774_);
v___x_3776_ = v___x_3771_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
else
{
lean_object* v___x_3778_; 
lean_del_object(v___x_3771_);
lean_inc_ref(v_e_3727_);
v___x_3778_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3727_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
if (lean_obj_tag(v_a_3779_) == 1)
{
lean_object* v_val_3780_; lean_object* v___x_3781_; lean_object* v_a_3782_; uint8_t v___x_3783_; 
v_val_3780_ = lean_ctor_get(v_a_3779_, 0);
lean_inc(v_val_3780_);
lean_dec_ref(v_a_3779_);
v___x_3781_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3753_, v___y_3763_);
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = lean_unbox(v_a_3782_);
lean_dec(v_a_3782_);
if (v___x_3783_ == 0)
{
v___y_3743_ = v_val_3780_;
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3757_;
v___y_3746_ = v___y_3759_;
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___y_3762_;
v___y_3749_ = v___y_3763_;
v___y_3750_ = v___y_3764_;
goto v___jp_3742_;
}
else
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lean_Meta_Grind_updateLastTag(v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref(v___x_3784_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3763_);
lean_inc(v___y_3762_);
lean_inc_ref(v___y_3761_);
lean_inc(v_val_3780_);
v___x_3785_ = lean_infer_type(v_val_3780_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref(v___x_3785_);
v___x_3787_ = l_Lean_MessageData_ofExpr(v_a_3786_);
v___x_3788_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3753_, v___x_3787_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref(v___x_3788_);
v___y_3743_ = v_val_3780_;
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3757_;
v___y_3746_ = v___y_3759_;
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___y_3762_;
v___y_3749_ = v___y_3763_;
v___y_3750_ = v___y_3764_;
goto v___jp_3742_;
}
else
{
lean_dec(v_val_3780_);
lean_dec_ref(v_e_3727_);
return v___x_3788_;
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v_val_3780_);
lean_dec_ref(v_e_3727_);
v_a_3789_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3785_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3785_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_dec(v_val_3780_);
lean_dec_ref(v_e_3727_);
return v___x_3784_;
}
}
}
else
{
lean_object* v___x_3797_; 
lean_dec(v_a_3779_);
v___x_3797_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3757_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; uint8_t v_verbose_3799_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
v_verbose_3799_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*11 + 15);
lean_dec(v_a_3798_);
if (v_verbose_3799_ == 0)
{
lean_dec_ref(v_e_3727_);
goto v___jp_3739_;
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3800_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3801_ = l_Lean_indentExpr(v_e_3727_);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3800_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = l_Lean_Meta_Grind_reportIssue(v___x_3802_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_dec_ref(v___x_3803_);
goto v___jp_3739_;
}
else
{
return v___x_3803_;
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec_ref(v_e_3727_);
v_a_3804_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3797_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3797_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_e_3727_);
v_a_3812_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3778_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3778_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v_e_3727_);
v_a_3821_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3768_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3768_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
lean_object* v___x_3829_; 
lean_inc_ref(v_e_3727_);
v___x_3829_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3727_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3840_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3840_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3840_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_unbox(v_a_3830_);
lean_dec(v_a_3830_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
lean_del_object(v___x_3832_);
v___x_3835_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3727_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
return v___x_3835_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
lean_dec_ref(v_e_3727_);
v___x_3836_ = lean_box(0);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3836_);
v___x_3838_ = v___x_3832_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v_e_3727_);
v_a_3841_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3829_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3829_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_e_3727_);
v_a_3849_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3765_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3765_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec(v_a_3866_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3880_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3881_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3879_, v___x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object* v_a_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___x_3896_; 
lean_inc_ref(v_e_3884_);
v___x_3896_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3884_, v_a_3885_, v_a_3889_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3926_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3926_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3926_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
uint8_t v___x_3901_; 
v___x_3901_ = lean_unbox(v_a_3897_);
lean_dec(v_a_3897_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
lean_dec_ref(v_e_3884_);
v___x_3902_ = lean_box(0);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3902_);
v___x_3904_ = v___x_3899_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
else
{
lean_object* v___x_3906_; 
lean_del_object(v___x_3899_);
lean_inc_ref(v_e_3884_);
v___x_3906_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3917_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3917_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3917_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
uint8_t v___x_3911_; 
v___x_3911_ = lean_unbox(v_a_3907_);
lean_dec(v_a_3907_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; 
lean_del_object(v___x_3909_);
v___x_3912_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
return v___x_3912_;
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec_ref(v_e_3884_);
v___x_3913_ = lean_box(0);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3913_);
v___x_3915_ = v___x_3909_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v_e_3884_);
v_a_3918_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3906_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3906_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v_e_3884_);
v_a_3927_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3896_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3896_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec(v_a_3936_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3950_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3951_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3949_, v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object* v_a_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
return v_res_3953_;
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
