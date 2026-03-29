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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchCond"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "satifised"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__8;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nthe following equality is false"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__9 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__9_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__10;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
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
v___x_106_ = lean_panic_fn_borrowed(v___x_105_, v_msg_104_);
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
lean_inc_n(v_val_436_, 2);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
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
lean_inc_n(v_fst_451_, 2);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
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
lean_inc_ref_n(v_self_778_, 2);
lean_dec(v_a_727_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_env_1044_; lean_object* v___x_1045_; lean_object* v_mctx_1046_; lean_object* v_lctx_1047_; lean_object* v_options_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1043_ = lean_st_ref_get(v___y_1041_);
v_env_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc_ref(v_env_1044_);
lean_dec(v___x_1043_);
v___x_1045_ = lean_st_ref_get(v___y_1039_);
v_mctx_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc_ref(v_mctx_1046_);
lean_dec(v___x_1045_);
v_lctx_1047_ = lean_ctor_get(v___y_1038_, 2);
v_options_1048_ = lean_ctor_get(v___y_1040_, 2);
lean_inc_ref(v_options_1048_);
lean_inc_ref(v_lctx_1047_);
v___x_1049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1049_, 0, v_env_1044_);
lean_ctor_set(v___x_1049_, 1, v_mctx_1046_);
lean_ctor_set(v___x_1049_, 2, v_lctx_1047_);
lean_ctor_set(v___x_1049_, 3, v_options_1048_);
v___x_1050_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_msgData_1037_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1059_; double v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_float_of_nat(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_ref_1071_; lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1117_; 
v_ref_1071_ = lean_ctor_get(v___y_1068_, 5);
v___x_1072_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1117_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1117_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v_traceState_1078_; lean_object* v_env_1079_; lean_object* v_nextMacroScope_1080_; lean_object* v_ngen_1081_; lean_object* v_auxDeclNGen_1082_; lean_object* v_cache_1083_; lean_object* v_messages_1084_; lean_object* v_infoState_1085_; lean_object* v_snapshotTasks_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1116_; 
v___x_1077_ = lean_st_ref_take(v___y_1069_);
v_traceState_1078_ = lean_ctor_get(v___x_1077_, 4);
v_env_1079_ = lean_ctor_get(v___x_1077_, 0);
v_nextMacroScope_1080_ = lean_ctor_get(v___x_1077_, 1);
v_ngen_1081_ = lean_ctor_get(v___x_1077_, 2);
v_auxDeclNGen_1082_ = lean_ctor_get(v___x_1077_, 3);
v_cache_1083_ = lean_ctor_get(v___x_1077_, 5);
v_messages_1084_ = lean_ctor_get(v___x_1077_, 6);
v_infoState_1085_ = lean_ctor_get(v___x_1077_, 7);
v_snapshotTasks_1086_ = lean_ctor_get(v___x_1077_, 8);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1088_ = v___x_1077_;
v_isShared_1089_ = v_isSharedCheck_1116_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snapshotTasks_1086_);
lean_inc(v_infoState_1085_);
lean_inc(v_messages_1084_);
lean_inc(v_cache_1083_);
lean_inc(v_traceState_1078_);
lean_inc(v_auxDeclNGen_1082_);
lean_inc(v_ngen_1081_);
lean_inc(v_nextMacroScope_1080_);
lean_inc(v_env_1079_);
lean_dec(v___x_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1116_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint64_t v_tid_1090_; lean_object* v_traces_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1115_; 
v_tid_1090_ = lean_ctor_get_uint64(v_traceState_1078_, sizeof(void*)*1);
v_traces_1091_ = lean_ctor_get(v_traceState_1078_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_traceState_1078_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1093_ = v_traceState_1078_;
v_isShared_1094_ = v_isSharedCheck_1115_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_traces_1091_);
lean_dec(v_traceState_1078_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1115_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; double v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1097_ = 0;
v___x_1098_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1099_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1099_, 0, v_cls_1064_);
lean_ctor_set(v___x_1099_, 1, v___x_1095_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
lean_ctor_set_float(v___x_1099_, sizeof(void*)*3, v___x_1096_);
lean_ctor_set_float(v___x_1099_, sizeof(void*)*3 + 8, v___x_1096_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*3 + 16, v___x_1097_);
v___x_1100_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1101_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v_a_1073_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
lean_inc(v_ref_1071_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_ref_1071_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_PersistentArray_push___redArg(v_traces_1091_, v___x_1102_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1103_);
v___x_1105_ = v___x_1093_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1103_);
lean_ctor_set_uint64(v_reuseFailAlloc_1114_, sizeof(void*)*1, v_tid_1090_);
v___x_1105_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v___x_1105_);
v___x_1107_ = v___x_1088_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_env_1079_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_nextMacroScope_1080_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_ngen_1081_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_auxDeclNGen_1082_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v_cache_1083_);
lean_ctor_set(v_reuseFailAlloc_1113_, 6, v_messages_1084_);
lean_ctor_set(v_reuseFailAlloc_1113_, 7, v_infoState_1085_);
lean_ctor_set(v_reuseFailAlloc_1113_, 8, v_snapshotTasks_1086_);
v___x_1107_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = lean_st_ref_set(v___y_1069_, v___x_1107_);
v___x_1109_ = lean_box(0);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1109_);
v___x_1111_ = v___x_1075_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1118_, v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3));
v___x_1137_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__5));
v___x_1138_ = l_Lean_Name_append(v___x_1137_, v___x_1136_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__8(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__7));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__10(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__9));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1218_; 
v_snd_1158_ = lean_ctor_get(v_b_1146_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_b_1146_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_b_1146_, 0);
lean_dec(v_unused_1219_);
v___x_1160_ = v_b_1146_;
v_isShared_1161_ = v_isSharedCheck_1218_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_dec(v_b_1146_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1218_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_box(0);
if (lean_obj_tag(v_snd_1158_) == 7)
{
lean_object* v_binderType_1170_; lean_object* v_body_1171_; lean_object* v___x_1172_; 
v_binderType_1170_ = lean_ctor_get(v_snd_1158_, 1);
v_body_1171_ = lean_ctor_get(v_snd_1158_, 2);
lean_inc_ref(v_binderType_1170_);
v___x_1172_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1170_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; uint8_t v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = lean_unbox(v_a_1173_);
lean_dec(v_a_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_inc_ref(v_body_1171_);
lean_dec_ref(v_snd_1158_);
lean_del_object(v___x_1160_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1169_);
lean_ctor_set(v___x_1175_, 1, v_body_1171_);
v_b_1146_ = v___x_1175_;
goto _start;
}
else
{
lean_object* v_options_1177_; uint8_t v_hasTrace_1178_; 
v_options_1177_ = lean_ctor_get(v___y_1155_, 2);
v_hasTrace_1178_ = lean_ctor_get_uint8(v_options_1177_, sizeof(void*)*1);
if (v_hasTrace_1178_ == 0)
{
goto v___jp_1162_;
}
else
{
lean_object* v_inheritedTraceOptions_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_inheritedTraceOptions_1179_ = lean_ctor_get(v___y_1155_, 13);
v___x_1180_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3));
v___x_1181_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6);
v___x_1182_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1179_, v_options_1177_, v___x_1181_);
if (v___x_1182_ == 0)
{
goto v___jp_1162_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Meta_Grind_updateLastTag(v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v___x_1183_);
v___x_1184_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__8);
lean_inc_ref(v_snd_1158_);
v___x_1185_ = l_Lean_indentExpr(v_snd_1158_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__10, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__10_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__10);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
lean_inc_ref(v_binderType_1170_);
v___x_1189_ = l_Lean_indentExpr(v_binderType_1170_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1180_, v___x_1190_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_dec_ref(v___x_1191_);
goto v___jp_1162_;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_snd_1158_);
lean_del_object(v___x_1160_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_snd_1158_);
lean_del_object(v___x_1160_);
v_a_1200_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1183_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1183_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v_snd_1158_);
lean_del_object(v___x_1160_);
v_a_1208_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1172_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1172_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_del_object(v___x_1160_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1169_);
lean_ctor_set(v___x_1216_, 1, v_snd_1158_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1162_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1163_ = lean_box(v___x_1145_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1164_);
v___x_1166_ = v___x_1160_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_snd_1158_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v___x_28700__boxed_1233_; lean_object* v_res_1234_; 
v___x_28700__boxed_1233_ = lean_unbox(v___x_1220_);
v_res_1234_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_28700__boxed_1233_, v_b_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1235_, v_a_1243_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1290_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1290_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1290_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = l_Lean_Expr_cleanupAnnotations(v_a_1248_);
v___x_1259_ = l_Lean_Expr_isApp(v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec_ref(v___x_1258_);
goto v___jp_1252_;
}
else
{
lean_object* v_arg_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_arg_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc_ref(v_arg_1260_);
v___x_1261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1258_);
v___x_1262_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1263_ = l_Lean_Expr_isConstOf(v___x_1261_, v___x_1262_);
lean_dec_ref(v___x_1261_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v_arg_1260_);
goto v___jp_1252_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_del_object(v___x_1250_);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v_arg_1260_);
v___x_1266_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_1263_, v___x_1265_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1281_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_fst_1271_; 
v_fst_1271_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_fst_1271_);
lean_dec(v_a_1267_);
if (lean_obj_tag(v_fst_1271_) == 0)
{
uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = 0;
v___x_1273_ = lean_box(v___x_1272_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1273_);
v___x_1275_ = v___x_1269_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v_val_1277_; lean_object* v___x_1279_; 
v_val_1277_ = lean_ctor_get(v_fst_1271_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v_fst_1271_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_val_1277_);
v___x_1279_ = v___x_1269_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_val_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1266_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1266_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
v___jp_1252_:
{
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = 0;
v___x_1254_ = lean_box(v___x_1253_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1254_);
v___x_1256_ = v___x_1250_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1247_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1247_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec(v_a_1300_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1312_, v_msg_1313_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1326_, lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1326_, v_msg_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v_b_1347_, lean_object* v_c_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc(v___y_1341_);
v___x_1354_ = lean_apply_13(v_k_1340_, v_b_1347_, v_c_1348_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, lean_box(0));
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v_b_1362_, lean_object* v_c_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v_b_1362_, v_c_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1370_, lean_object* v_k_1371_, uint8_t v_cleanupAnnotations_1372_, uint8_t v_whnfType_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___f_1385_; lean_object* v___x_1386_; 
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc(v___y_1374_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1385_, 0, v_k_1371_);
lean_closure_set(v___f_1385_, 1, v___y_1374_);
lean_closure_set(v___f_1385_, 2, v___y_1375_);
lean_closure_set(v___f_1385_, 3, v___y_1376_);
lean_closure_set(v___f_1385_, 4, v___y_1377_);
lean_closure_set(v___f_1385_, 5, v___y_1378_);
lean_closure_set(v___f_1385_, 6, v___y_1379_);
v___x_1386_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1370_, v___f_1385_, v_cleanupAnnotations_1372_, v_whnfType_1373_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1386_) == 0)
{
return v___x_1386_;
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1395_, lean_object* v_k_1396_, lean_object* v_cleanupAnnotations_1397_, lean_object* v_whnfType_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1410_; uint8_t v_whnfType_boxed_1411_; lean_object* v_res_1412_; 
v_cleanupAnnotations_boxed_1410_ = lean_unbox(v_cleanupAnnotations_1397_);
v_whnfType_boxed_1411_ = lean_unbox(v_whnfType_1398_);
v_res_1412_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1395_, v_k_1396_, v_cleanupAnnotations_boxed_1410_, v_whnfType_boxed_1411_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec(v___y_1399_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1413_, lean_object* v_type_1414_, lean_object* v_k_1415_, uint8_t v_cleanupAnnotations_1416_, uint8_t v_whnfType_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1414_, v_k_1415_, v_cleanupAnnotations_1416_, v_whnfType_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_type_1431_, lean_object* v_k_1432_, lean_object* v_cleanupAnnotations_1433_, lean_object* v_whnfType_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1446_; uint8_t v_whnfType_boxed_1447_; lean_object* v_res_1448_; 
v_cleanupAnnotations_boxed_1446_ = lean_unbox(v_cleanupAnnotations_1433_);
v_whnfType_boxed_1447_ = lean_unbox(v_whnfType_1434_);
v_res_1448_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1430_, v_type_1431_, v_k_1432_, v_cleanupAnnotations_boxed_1446_, v_whnfType_boxed_1447_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec(v___y_1435_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* v_e_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_xs_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_a_110572__boxed_1468_; lean_object* v_res_1469_; 
v_a_110572__boxed_1468_ = lean_unbox(v_a_1453_);
v_res_1469_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1452_, v_a_110572__boxed_1468_, v_a_1454_, v_xs_1455_, v_x_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v_x_1456_);
lean_dec_ref(v_xs_1455_);
return v_res_1469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1479_, lean_object* v_h_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
uint8_t v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; uint8_t v___y_1500_; uint8_t v___y_1501_; lean_object* v_h_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v_options_1882_; uint8_t v_hasTrace_1883_; 
v_options_1882_ = lean_ctor_get(v_a_1489_, 2);
v_hasTrace_1883_ = lean_ctor_get_uint8(v_options_1882_, sizeof(void*)*1);
if (v_hasTrace_1883_ == 0)
{
v___y_1766_ = v_a_1481_;
v___y_1767_ = v_a_1482_;
v___y_1768_ = v_a_1483_;
v___y_1769_ = v_a_1484_;
v___y_1770_ = v_a_1485_;
v___y_1771_ = v_a_1486_;
v___y_1772_ = v_a_1487_;
v___y_1773_ = v_a_1488_;
v___y_1774_ = v_a_1489_;
v___y_1775_ = v_a_1490_;
goto v___jp_1765_;
}
else
{
lean_object* v_inheritedTraceOptions_1884_; lean_object* v_cls_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_inheritedTraceOptions_1884_ = lean_ctor_get(v_a_1489_, 13);
v_cls_1885_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3));
v___x_1886_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6);
v___x_1887_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1884_, v_options_1882_, v___x_1886_);
if (v___x_1887_ == 0)
{
v___y_1766_ = v_a_1481_;
v___y_1767_ = v_a_1482_;
v___y_1768_ = v_a_1483_;
v___y_1769_ = v_a_1484_;
v___y_1770_ = v_a_1485_;
v___y_1771_ = v_a_1486_;
v___y_1772_ = v_a_1487_;
v___y_1773_ = v_a_1488_;
v___y_1774_ = v_a_1489_;
v___y_1775_ = v_a_1490_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Meta_Grind_updateLastTag(v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v___x_1889_; 
lean_dec_ref(v___x_1888_);
lean_inc(v_a_1490_);
lean_inc_ref(v_a_1489_);
lean_inc(v_a_1488_);
lean_inc_ref(v_a_1487_);
lean_inc_ref(v_h_1480_);
v___x_1889_ = lean_infer_type(v_h_1480_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
v___x_1891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1892_ = l_Lean_MessageData_ofExpr(v_a_1890_);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1885_, v___x_1893_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_dec_ref(v___x_1894_);
v___y_1766_ = v_a_1481_;
v___y_1767_ = v_a_1482_;
v___y_1768_ = v_a_1483_;
v___y_1769_ = v_a_1484_;
v___y_1770_ = v_a_1485_;
v___y_1771_ = v_a_1486_;
v___y_1772_ = v_a_1487_;
v___y_1773_ = v_a_1488_;
v___y_1774_ = v_a_1489_;
v___y_1775_ = v_a_1490_;
goto v___jp_1765_;
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
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
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1903_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1889_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1889_);
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
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1911_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1888_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1888_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
v___jp_1492_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
v___jp_1495_:
{
if (v___y_1500_ == 0)
{
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_e_1479_);
if (v___y_1501_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v___y_1497_);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_inc_ref(v___y_1499_);
v___x_1515_ = l_Lean_Meta_normLitValue(v___y_1499_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
lean_inc_ref(v___y_1497_);
v___x_1517_ = l_Lean_Meta_normLitValue(v___y_1497_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1557_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1557_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1557_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_expr_eqv(v_a_1516_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec(v_a_1516_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_del_object(v___x_1520_);
v___x_1523_ = l_Lean_Meta_mkEq(v___y_1499_, v___y_1497_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = l_Lean_mkNot(v_a_1524_);
v___x_1526_ = l_Lean_Meta_mkDecideProof(v___x_1525_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1536_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = l_Lean_Expr_app___override(v_a_1527_, v_h_1502_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v_h_1502_);
v_a_1537_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1526_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1526_);
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
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_h_1502_);
v_a_1545_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1523_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1523_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v___y_1497_);
v___x_1553_ = lean_box(0);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1553_);
v___x_1555_ = v___x_1520_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_a_1516_);
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v___y_1497_);
v_a_1558_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1517_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1517_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v___y_1497_);
v_a_1566_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1515_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1515_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1499_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1665_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1665_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1665_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
if (lean_obj_tag(v_a_1575_) == 1)
{
lean_object* v_val_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1577_);
v_val_1579_ = lean_ctor_get(v_a_1575_, 0);
lean_inc(v_val_1579_);
lean_dec_ref(v_a_1575_);
v___x_1580_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1497_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1652_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1652_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1652_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_val_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1647_; 
lean_del_object(v___x_1583_);
v_val_1585_ = lean_ctor_get(v_a_1581_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1581_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1587_ = v_a_1581_;
v_isShared_1588_ = v_isSharedCheck_1647_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_val_1585_);
lean_dec(v_a_1581_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1647_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_mkNoConfusion(v___y_1498_, v_h_1502_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_toConstantVal_1590_; lean_object* v_toConstantVal_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1638_; 
v_toConstantVal_1590_ = lean_ctor_get(v_val_1579_, 0);
lean_inc_ref(v_toConstantVal_1590_);
lean_dec(v_val_1579_);
v_toConstantVal_1591_ = lean_ctor_get(v_val_1585_, 0);
lean_inc_ref(v_toConstantVal_1591_);
lean_dec(v_val_1585_);
v_a_1592_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1594_ = v___x_1589_;
v_isShared_1595_ = v_isSharedCheck_1638_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1589_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1638_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_name_1596_; lean_object* v_name_1597_; uint8_t v___x_1598_; 
v_name_1596_ = lean_ctor_get(v_toConstantVal_1590_, 0);
lean_inc(v_name_1596_);
lean_dec_ref(v_toConstantVal_1590_);
v_name_1597_ = lean_ctor_get(v_toConstantVal_1591_, 0);
lean_inc(v_name_1597_);
lean_dec_ref(v_toConstantVal_1591_);
v___x_1598_ = lean_name_eq(v_name_1596_, v_name_1597_);
lean_dec(v_name_1597_);
lean_dec(v_name_1596_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref(v_e_1479_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_a_1592_);
v___x_1600_ = v___x_1587_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1592_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1600_);
v___x_1602_ = v___x_1594_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_object* v___x_1605_; 
lean_del_object(v___x_1594_);
lean_del_object(v___x_1587_);
lean_inc(v___y_1512_);
lean_inc_ref(v___y_1511_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v_a_1592_);
v___x_1605_ = lean_infer_type(v_a_1592_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_Lean_Meta_whnfD(v_a_1606_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1621_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
if (lean_obj_tag(v_a_1608_) == 7)
{
lean_object* v_binderType_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; 
lean_del_object(v___x_1610_);
v_binderType_1612_ = lean_ctor_get(v_a_1608_, 1);
lean_inc_ref(v_binderType_1612_);
lean_dec_ref(v_a_1608_);
v___x_1613_ = lean_box(v___y_1496_);
v___f_1614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1614_, 0, v_e_1479_);
lean_closure_set(v___f_1614_, 1, v___x_1613_);
lean_closure_set(v___f_1614_, 2, v_a_1592_);
v___x_1615_ = 0;
v___x_1616_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1612_, v___f_1614_, v___x_1615_, v___x_1615_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1592_);
lean_dec_ref(v_e_1479_);
v___x_1617_ = lean_box(0);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1617_);
v___x_1619_ = v___x_1610_;
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
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1592_);
lean_dec_ref(v_e_1479_);
v_a_1622_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1607_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1607_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1592_);
lean_dec_ref(v_e_1479_);
v_a_1630_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1605_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1605_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_del_object(v___x_1587_);
lean_dec(v_val_1585_);
lean_dec(v_val_1579_);
lean_dec_ref(v_e_1479_);
v_a_1639_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1589_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1589_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec(v_a_1581_);
lean_dec(v_val_1579_);
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_e_1479_);
v___x_1648_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1648_);
v___x_1650_ = v___x_1583_;
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
lean_dec(v_val_1579_);
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_e_1479_);
v_a_1653_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1580_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1580_);
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
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_a_1575_);
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec_ref(v_e_1479_);
v___x_1661_ = lean_box(0);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1661_);
v___x_1663_ = v___x_1577_;
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
lean_dec_ref(v_h_1502_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec_ref(v_e_1479_);
v_a_1666_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1574_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1574_);
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
}
v___jp_1674_:
{
lean_object* v_self_1690_; uint8_t v_interpreted_1691_; uint8_t v_ctor_1692_; lean_object* v___x_1693_; 
v_self_1690_ = lean_ctor_get(v___y_1676_, 0);
lean_inc_ref_n(v_self_1690_, 2);
v_interpreted_1691_ = lean_ctor_get_uint8(v___y_1676_, sizeof(void*)*11 + 1);
v_ctor_1692_ = lean_ctor_get_uint8(v___y_1676_, sizeof(void*)*11 + 2);
lean_dec_ref(v___y_1676_);
lean_inc_ref(v___y_1677_);
v___x_1693_ = l_Lean_Meta_Grind_hasSameType(v_self_1690_, v___y_1677_, v___y_1678_, v___y_1686_, v___y_1679_, v___y_1684_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1756_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1756_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1756_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_unbox(v_a_1694_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v___x_1699_ = lean_box(0);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
lean_del_object(v___x_1696_);
if (v___y_1689_ == 0)
{
lean_object* v___x_1703_; 
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1688_);
lean_inc(v___y_1685_);
lean_inc_ref(v_self_1690_);
v___x_1703_ = lean_grind_mk_eq_proof(v_self_1690_, v___y_1675_, v___y_1685_, v___y_1688_, v___y_1681_, v___y_1687_, v___y_1682_, v___y_1683_, v___y_1678_, v___y_1686_, v___y_1679_, v___y_1684_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = l_Lean_Meta_mkEqTrans(v_a_1704_, v_h_1480_, v___y_1678_, v___y_1686_, v___y_1679_, v___y_1684_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
v___y_1496_ = v___x_1707_;
v___y_1497_ = v___y_1677_;
v___y_1498_ = v___y_1680_;
v___y_1499_ = v_self_1690_;
v___y_1500_ = v_ctor_1692_;
v___y_1501_ = v_interpreted_1691_;
v_h_1502_ = v_a_1706_;
v___y_1503_ = v___y_1685_;
v___y_1504_ = v___y_1688_;
v___y_1505_ = v___y_1681_;
v___y_1506_ = v___y_1687_;
v___y_1507_ = v___y_1682_;
v___y_1508_ = v___y_1683_;
v___y_1509_ = v___y_1678_;
v___y_1510_ = v___y_1686_;
v___y_1511_ = v___y_1679_;
v___y_1512_ = v___y_1684_;
goto v___jp_1495_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_e_1479_);
v_a_1708_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1705_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1716_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1703_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1703_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v___x_1724_; 
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1688_);
lean_inc(v___y_1685_);
lean_inc_ref(v_self_1690_);
v___x_1724_ = lean_grind_mk_heq_proof(v_self_1690_, v___y_1675_, v___y_1685_, v___y_1688_, v___y_1681_, v___y_1687_, v___y_1682_, v___y_1683_, v___y_1678_, v___y_1686_, v___y_1679_, v___y_1684_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l_Lean_Meta_mkHEqTrans(v_a_1725_, v_h_1480_, v___y_1678_, v___y_1686_, v___y_1679_, v___y_1684_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = 0;
v___x_1729_ = l_Lean_Meta_mkEqOfHEq(v_a_1727_, v___x_1728_, v___y_1678_, v___y_1686_, v___y_1679_, v___y_1684_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; uint8_t v___x_1731_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
v___y_1496_ = v___x_1731_;
v___y_1497_ = v___y_1677_;
v___y_1498_ = v___y_1680_;
v___y_1499_ = v_self_1690_;
v___y_1500_ = v_ctor_1692_;
v___y_1501_ = v_interpreted_1691_;
v_h_1502_ = v_a_1730_;
v___y_1503_ = v___y_1685_;
v___y_1504_ = v___y_1688_;
v___y_1505_ = v___y_1681_;
v___y_1506_ = v___y_1687_;
v___y_1507_ = v___y_1682_;
v___y_1508_ = v___y_1683_;
v___y_1509_ = v___y_1678_;
v___y_1510_ = v___y_1686_;
v___y_1511_ = v___y_1679_;
v___y_1512_ = v___y_1684_;
goto v___jp_1495_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_e_1479_);
v_a_1732_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1729_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1729_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_e_1479_);
v_a_1740_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1726_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1726_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1748_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1724_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1724_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v_self_1690_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1757_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1693_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1693_);
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
v___jp_1765_:
{
lean_object* v___x_1776_; 
lean_inc(v___y_1775_);
lean_inc_ref(v___y_1774_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc_ref(v_h_1480_);
v___x_1776_ = lean_infer_type(v_h_1480_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1873_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1873_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1873_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1777_);
if (lean_obj_tag(v___x_1781_) == 1)
{
lean_object* v_val_1782_; lean_object* v_snd_1783_; lean_object* v_fst_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1779_);
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v___x_1781_);
v_snd_1783_ = lean_ctor_get(v_val_1782_, 1);
v_fst_1784_ = lean_ctor_get(v_val_1782_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_val_1782_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1786_ = v_val_1782_;
v_isShared_1787_ = v_isSharedCheck_1868_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_snd_1783_);
lean_inc(v_fst_1784_);
lean_dec(v_val_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1868_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_fst_1788_; lean_object* v_snd_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1867_; 
v_fst_1788_ = lean_ctor_get(v_snd_1783_, 0);
v_snd_1789_ = lean_ctor_get(v_snd_1783_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_snd_1783_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1791_ = v_snd_1783_;
v_isShared_1792_ = v_isSharedCheck_1867_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_snd_1789_);
lean_inc(v_fst_1788_);
lean_dec(v_snd_1783_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1867_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v_mvarId_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1865_; 
v___x_1793_ = lean_st_ref_get(v___y_1766_);
v_mvarId_1794_ = lean_ctor_get(v___x_1793_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1793_, 0);
lean_dec(v_unused_1866_);
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1865_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_mvarId_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1865_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_MVarId_getType(v_mvarId_1794_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_1788_, v___y_1771_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1801_, v___y_1766_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
if (lean_obj_tag(v_a_1803_) == 1)
{
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1786_);
if (lean_obj_tag(v_fst_1784_) == 0)
{
lean_object* v_val_1804_; uint8_t v___x_1805_; 
v_val_1804_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_val_1804_);
lean_dec_ref(v_a_1803_);
v___x_1805_ = 0;
v___y_1675_ = v_a_1801_;
v___y_1676_ = v_val_1804_;
v___y_1677_ = v_snd_1789_;
v___y_1678_ = v___y_1772_;
v___y_1679_ = v___y_1774_;
v___y_1680_ = v_a_1799_;
v___y_1681_ = v___y_1768_;
v___y_1682_ = v___y_1770_;
v___y_1683_ = v___y_1771_;
v___y_1684_ = v___y_1775_;
v___y_1685_ = v___y_1766_;
v___y_1686_ = v___y_1773_;
v___y_1687_ = v___y_1769_;
v___y_1688_ = v___y_1767_;
v___y_1689_ = v___x_1805_;
goto v___jp_1674_;
}
else
{
lean_object* v_val_1806_; uint8_t v___x_1807_; 
lean_dec_ref(v_fst_1784_);
v_val_1806_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_val_1806_);
lean_dec_ref(v_a_1803_);
v___x_1807_ = 1;
v___y_1675_ = v_a_1801_;
v___y_1676_ = v_val_1806_;
v___y_1677_ = v_snd_1789_;
v___y_1678_ = v___y_1772_;
v___y_1679_ = v___y_1774_;
v___y_1680_ = v_a_1799_;
v___y_1681_ = v___y_1768_;
v___y_1682_ = v___y_1770_;
v___y_1683_ = v___y_1771_;
v___y_1684_ = v___y_1775_;
v___y_1685_ = v___y_1766_;
v___y_1686_ = v___y_1773_;
v___y_1687_ = v___y_1769_;
v___y_1688_ = v___y_1767_;
v___y_1689_ = v___x_1807_;
goto v___jp_1674_;
}
}
else
{
lean_object* v___x_1808_; 
lean_dec(v_a_1803_);
lean_dec(v_a_1799_);
lean_dec(v_snd_1789_);
lean_dec(v_fst_1784_);
lean_dec_ref(v_h_1480_);
v___x_1808_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1770_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; uint8_t v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v___x_1810_ = lean_unbox(v_a_1809_);
lean_dec(v_a_1809_);
if (v___x_1810_ == 0)
{
lean_dec(v_a_1801_);
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1786_);
lean_dec_ref(v_e_1479_);
goto v___jp_1492_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1812_ = l_Lean_indentExpr(v_a_1801_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 7);
lean_ctor_set(v___x_1796_, 1, v___x_1812_);
lean_ctor_set(v___x_1796_, 0, v___x_1811_);
v___x_1814_ = v___x_1796_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 7);
lean_ctor_set(v___x_1791_, 1, v___x_1815_);
lean_ctor_set(v___x_1791_, 0, v___x_1814_);
v___x_1817_ = v___x_1791_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = l_Lean_indentExpr(v_e_1479_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 7);
lean_ctor_set(v___x_1786_, 1, v___x_1818_);
lean_ctor_set(v___x_1786_, 0, v___x_1817_);
v___x_1820_ = v___x_1786_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Meta_Sym_reportIssue(v___x_1820_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_dec_ref(v___x_1821_);
goto v___jp_1492_;
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
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
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_a_1801_);
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1786_);
lean_dec_ref(v_e_1479_);
v_a_1833_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1808_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1808_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1801_);
lean_dec(v_a_1799_);
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_dec(v_snd_1789_);
lean_del_object(v___x_1786_);
lean_dec(v_fst_1784_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1841_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1802_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1802_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1799_);
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_dec(v_snd_1789_);
lean_del_object(v___x_1786_);
lean_dec(v_fst_1784_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1849_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1800_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1800_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_dec(v_snd_1789_);
lean_dec(v_fst_1788_);
lean_del_object(v___x_1786_);
lean_dec(v_fst_1784_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1857_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1798_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1798_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec(v___x_1781_);
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v___x_1869_ = lean_box(0);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1869_);
v___x_1871_ = v___x_1779_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
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
lean_dec_ref(v_h_1480_);
lean_dec_ref(v_e_1479_);
v_a_1874_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1776_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1776_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_1919_, lean_object* v_xs_1920_, uint8_t v_a_1921_, lean_object* v_a_1922_, lean_object* v_as_1923_, size_t v_sz_1924_, size_t v_i_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_usize_dec_lt(v_i_1925_, v_sz_1924_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v_a_1922_);
lean_dec_ref(v_e_1919_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_b_1926_);
return v___x_1939_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v_b_1926_);
v_a_1940_ = lean_array_uget_borrowed(v_as_1923_, v_i_1925_);
lean_inc(v_a_1940_);
lean_inc_ref(v_e_1919_);
v___x_1941_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_1919_, v_a_1940_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = lean_box(0);
if (lean_obj_tag(v_a_1942_) == 1)
{
lean_object* v_val_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_e_1919_);
v_val_1944_ = lean_ctor_get(v_a_1942_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_a_1942_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1946_ = v_a_1942_;
v_isShared_1947_ = v_isSharedCheck_1973_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_val_1944_);
lean_dec(v_a_1942_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1973_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
uint8_t v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = 0;
v___x_1949_ = 1;
v___x_1950_ = l_Lean_Meta_mkLambdaFVars(v_xs_1920_, v_val_1944_, v___x_1948_, v_a_1921_, v___x_1948_, v_a_1921_, v___x_1949_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1964_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1964_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1964_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = l_Lean_Expr_app___override(v_a_1922_, v_a_1951_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1955_);
v___x_1957_ = v___x_1946_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v___x_1943_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1959_);
v___x_1961_ = v___x_1953_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_del_object(v___x_1946_);
lean_dec_ref(v_a_1922_);
v_a_1965_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1950_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1950_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
else
{
lean_object* v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; 
lean_dec(v_a_1942_);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_add(v_i_1925_, v___x_1975_);
v_i_1925_ = v___x_1976_;
v_b_1926_ = v___x_1974_;
goto _start;
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_a_1922_);
lean_dec_ref(v_e_1919_);
v_a_1978_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1941_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1941_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_1986_, uint8_t v_a_1987_, lean_object* v_a_1988_, lean_object* v_xs_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2004_ = lean_array_size(v_xs_1989_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_1986_, v_xs_1989_, v_a_1987_, v_a_1988_, v_xs_1989_, v_sz_2004_, v___x_2005_, v___x_2003_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2019_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2019_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2019_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_fst_2011_; 
v_fst_2011_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_fst_2011_);
lean_dec(v_a_2007_);
if (lean_obj_tag(v_fst_2011_) == 0)
{
lean_object* v___x_2013_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2002_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2002_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; 
v_val_2015_ = lean_ctor_get(v_fst_2011_, 0);
lean_inc(v_val_2015_);
lean_dec_ref(v_fst_2011_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_val_2015_);
v___x_2017_ = v___x_2009_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2006_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2006_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2028_ = _args[0];
lean_object* v_xs_2029_ = _args[1];
lean_object* v_a_2030_ = _args[2];
lean_object* v_a_2031_ = _args[3];
lean_object* v_as_2032_ = _args[4];
lean_object* v_sz_2033_ = _args[5];
lean_object* v_i_2034_ = _args[6];
lean_object* v_b_2035_ = _args[7];
lean_object* v___y_2036_ = _args[8];
lean_object* v___y_2037_ = _args[9];
lean_object* v___y_2038_ = _args[10];
lean_object* v___y_2039_ = _args[11];
lean_object* v___y_2040_ = _args[12];
lean_object* v___y_2041_ = _args[13];
lean_object* v___y_2042_ = _args[14];
lean_object* v___y_2043_ = _args[15];
lean_object* v___y_2044_ = _args[16];
lean_object* v___y_2045_ = _args[17];
lean_object* v___y_2046_ = _args[18];
_start:
{
uint8_t v_a_110596__boxed_2047_; size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_a_110596__boxed_2047_ = lean_unbox(v_a_2030_);
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2028_, v_xs_2029_, v_a_110596__boxed_2047_, v_a_2031_, v_as_2032_, v_sz_boxed_2048_, v_i_boxed_2049_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v_as_2032_);
lean_dec_ref(v_xs_2029_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2051_, lean_object* v_h_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2051_, v_h_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec(v_a_2053_);
return v_res_2064_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2067_ = l_Lean_stringToMessageData(v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2068_, lean_object* v_xs_2069_, uint8_t v___x_2070_, lean_object* v_as_2071_, size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_a_2087_; uint8_t v___x_2091_; 
v___x_2091_ = lean_usize_dec_lt(v_i_2073_, v_sz_2072_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref(v_e_2068_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_b_2074_);
return v___x_2092_;
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2094_; 
lean_dec_ref(v_b_2074_);
v_a_2093_ = lean_array_uget_borrowed(v_as_2071_, v_i_2073_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v_a_2093_);
v___x_2094_ = lean_infer_type(v_a_2093_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_n(v_a_2095_, 2);
lean_dec_ref(v___x_2094_);
v___x_2096_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2095_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; uint8_t v___x_2150_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = lean_box(0);
v___x_2099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2150_ = lean_unbox(v_a_2097_);
lean_dec(v_a_2097_);
if (v___x_2150_ == 0)
{
lean_dec(v_a_2095_);
v_a_2087_ = v___x_2099_;
goto v___jp_2086_;
}
else
{
lean_object* v_options_2151_; uint8_t v_hasTrace_2152_; 
v_options_2151_ = lean_ctor_get(v___y_2083_, 2);
v_hasTrace_2152_ = lean_ctor_get_uint8(v_options_2151_, sizeof(void*)*1);
if (v_hasTrace_2152_ == 0)
{
lean_dec(v_a_2095_);
v___y_2101_ = v___y_2075_;
v___y_2102_ = v___y_2076_;
v___y_2103_ = v___y_2077_;
v___y_2104_ = v___y_2078_;
v___y_2105_ = v___y_2079_;
v___y_2106_ = v___y_2080_;
v___y_2107_ = v___y_2081_;
v___y_2108_ = v___y_2082_;
v___y_2109_ = v___y_2083_;
v___y_2110_ = v___y_2084_;
goto v___jp_2100_;
}
else
{
lean_object* v_inheritedTraceOptions_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_inheritedTraceOptions_2153_ = lean_ctor_get(v___y_2083_, 13);
v___x_2154_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3));
v___x_2155_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6);
v___x_2156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2153_, v_options_2151_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_dec(v_a_2095_);
v___y_2101_ = v___y_2075_;
v___y_2102_ = v___y_2076_;
v___y_2103_ = v___y_2077_;
v___y_2104_ = v___y_2078_;
v___y_2105_ = v___y_2079_;
v___y_2106_ = v___y_2080_;
v___y_2107_ = v___y_2081_;
v___y_2108_ = v___y_2082_;
v___y_2109_ = v___y_2083_;
v___y_2110_ = v___y_2084_;
goto v___jp_2100_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Meta_Grind_updateLastTag(v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v___x_2157_);
v___x_2158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2159_ = l_Lean_MessageData_ofExpr(v_a_2095_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2154_, v___x_2160_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_dec_ref(v___x_2161_);
v___y_2101_ = v___y_2075_;
v___y_2102_ = v___y_2076_;
v___y_2103_ = v___y_2077_;
v___y_2104_ = v___y_2078_;
v___y_2105_ = v___y_2079_;
v___y_2106_ = v___y_2080_;
v___y_2107_ = v___y_2081_;
v___y_2108_ = v___y_2082_;
v___y_2109_ = v___y_2083_;
v___y_2110_ = v___y_2084_;
goto v___jp_2100_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_e_2068_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2095_);
lean_dec_ref(v_e_2068_);
v_a_2170_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2157_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2157_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
v___jp_2100_:
{
lean_object* v___x_2111_; 
lean_inc(v_a_2093_);
lean_inc_ref(v_e_2068_);
v___x_2111_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2068_, v_a_2093_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
if (lean_obj_tag(v_a_2112_) == 1)
{
lean_object* v_val_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_e_2068_);
v_val_2113_ = lean_ctor_get(v_a_2112_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2112_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2115_ = v_a_2112_;
v_isShared_2116_ = v_isSharedCheck_2141_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_val_2113_);
lean_dec(v_a_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2141_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = 0;
v___x_2118_ = 1;
v___x_2119_ = l_Lean_Meta_mkLambdaFVars(v_xs_2069_, v_val_2113_, v___x_2117_, v___x_2070_, v___x_2117_, v___x_2070_, v___x_2118_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2132_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2132_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2132_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_a_2120_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2098_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2127_);
v___x_2129_ = v___x_2122_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_del_object(v___x_2115_);
v_a_2133_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2119_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2119_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_dec(v_a_2112_);
v_a_2087_ = v___x_2099_;
goto v___jp_2086_;
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_e_2068_);
v_a_2142_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2111_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2111_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2095_);
lean_dec_ref(v_e_2068_);
v_a_2178_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2096_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2096_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_e_2068_);
v_a_2186_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2094_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2094_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
v___jp_2086_:
{
size_t v___x_2088_; size_t v___x_2089_; 
v___x_2088_ = ((size_t)1ULL);
v___x_2089_ = lean_usize_add(v_i_2073_, v___x_2088_);
lean_inc_ref(v_a_2087_);
v_i_2073_ = v___x_2089_;
v_b_2074_ = v_a_2087_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2194_ = _args[0];
lean_object* v_xs_2195_ = _args[1];
lean_object* v___x_2196_ = _args[2];
lean_object* v_as_2197_ = _args[3];
lean_object* v_sz_2198_ = _args[4];
lean_object* v_i_2199_ = _args[5];
lean_object* v_b_2200_ = _args[6];
lean_object* v___y_2201_ = _args[7];
lean_object* v___y_2202_ = _args[8];
lean_object* v___y_2203_ = _args[9];
lean_object* v___y_2204_ = _args[10];
lean_object* v___y_2205_ = _args[11];
lean_object* v___y_2206_ = _args[12];
lean_object* v___y_2207_ = _args[13];
lean_object* v___y_2208_ = _args[14];
lean_object* v___y_2209_ = _args[15];
lean_object* v___y_2210_ = _args[16];
lean_object* v___y_2211_ = _args[17];
_start:
{
uint8_t v___x_30362__boxed_2212_; size_t v_sz_boxed_2213_; size_t v_i_boxed_2214_; lean_object* v_res_2215_; 
v___x_30362__boxed_2212_ = lean_unbox(v___x_2196_);
v_sz_boxed_2213_ = lean_unbox_usize(v_sz_2198_);
lean_dec(v_sz_2198_);
v_i_boxed_2214_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2194_, v_xs_2195_, v___x_30362__boxed_2212_, v_as_2197_, v_sz_boxed_2213_, v_i_boxed_2214_, v_b_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v_as_2197_);
lean_dec_ref(v_xs_2195_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2216_, uint8_t v___x_2217_, lean_object* v_xs_2218_, lean_object* v_x_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_2235_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2233_ = lean_array_size(v_xs_2218_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2216_, v_xs_2218_, v___x_2217_, v_xs_2218_, v_sz_2233_, v___x_2234_, v___x_2232_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2248_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2248_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2248_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_fst_2240_; 
v_fst_2240_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_fst_2240_);
lean_dec(v_a_2236_);
if (lean_obj_tag(v_fst_2240_) == 0)
{
lean_object* v___x_2242_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2231_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2231_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2246_; 
v_val_2244_ = lean_ctor_get(v_fst_2240_, 0);
lean_inc(v_val_2244_);
lean_dec_ref(v_fst_2240_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_val_2244_);
v___x_2246_ = v___x_2238_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_val_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_a_2249_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2235_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2235_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2257_, lean_object* v___x_2258_, lean_object* v_xs_2259_, lean_object* v_x_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v___x_30614__boxed_2272_; lean_object* v_res_2273_; 
v___x_30614__boxed_2272_ = lean_unbox(v___x_2258_);
v_res_2273_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2257_, v___x_30614__boxed_2272_, v_xs_2259_, v_x_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v_x_2260_);
lean_dec_ref(v_xs_2259_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
lean_inc_ref(v_e_2274_);
v___x_2286_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2274_, v_a_2282_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2306_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2306_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2306_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = l_Lean_Expr_cleanupAnnotations(v_a_2287_);
v___x_2297_ = l_Lean_Expr_isApp(v___x_2296_);
if (v___x_2297_ == 0)
{
lean_dec_ref(v___x_2296_);
lean_dec_ref(v_e_2274_);
goto v___jp_2291_;
}
else
{
lean_object* v_arg_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v_arg_2298_ = lean_ctor_get(v___x_2296_, 1);
lean_inc_ref(v_arg_2298_);
v___x_2299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2296_);
v___x_2300_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2301_ = l_Lean_Expr_isConstOf(v___x_2299_, v___x_2300_);
lean_dec_ref(v___x_2299_);
if (v___x_2301_ == 0)
{
lean_dec_ref(v_arg_2298_);
lean_dec_ref(v_e_2274_);
goto v___jp_2291_;
}
else
{
lean_object* v___x_2302_; lean_object* v___f_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; 
lean_del_object(v___x_2289_);
v___x_2302_ = lean_box(v___x_2301_);
v___f_2303_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2303_, 0, v_e_2274_);
lean_closure_set(v___f_2303_, 1, v___x_2302_);
v___x_2304_ = 0;
v___x_2305_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2298_, v___f_2303_, v___x_2304_, v___x_2304_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
return v___x_2305_;
}
}
v___jp_2291_:
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2292_);
v___x_2294_ = v___x_2289_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
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
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_e_2274_);
v_a_2307_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2286_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2286_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec(v_a_2316_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; 
lean_inc_ref(v_e_2328_);
v___x_2340_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2328_, v_a_2329_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2408_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2408_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2408_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint8_t v_ctor_2345_; 
v_ctor_2345_ = lean_ctor_get_uint8(v_a_2341_, sizeof(void*)*11 + 2);
if (v_ctor_2345_ == 0)
{
uint8_t v_interpreted_2346_; 
v_interpreted_2346_ = lean_ctor_get_uint8(v_a_2341_, sizeof(void*)*11 + 1);
if (v_interpreted_2346_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_e_2328_);
v___x_2348_ = v___x_2343_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_e_2328_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
else
{
lean_object* v_self_2350_; lean_object* v___x_2352_; 
lean_dec_ref(v_e_2328_);
v_self_2350_ = lean_ctor_get(v_a_2341_, 0);
lean_inc_ref(v_self_2350_);
lean_dec(v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_self_2350_);
v___x_2352_ = v___x_2343_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_self_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
lean_object* v_self_2354_; lean_object* v___x_2355_; 
lean_del_object(v___x_2343_);
lean_dec_ref(v_e_2328_);
v_self_2354_ = lean_ctor_get(v_a_2341_, 0);
lean_inc_ref_n(v_self_2354_, 2);
lean_dec(v_a_2341_);
v___x_2355_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2354_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2399_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2399_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2399_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
if (lean_obj_tag(v_a_2356_) == 1)
{
lean_object* v_val_2360_; lean_object* v_numParams_2361_; lean_object* v_numFields_2362_; lean_object* v_nargs_2363_; lean_object* v___x_2364_; lean_object* v_dummy_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_del_object(v___x_2358_);
v_val_2360_ = lean_ctor_get(v_a_2356_, 0);
lean_inc(v_val_2360_);
lean_dec_ref(v_a_2356_);
v_numParams_2361_ = lean_ctor_get(v_val_2360_, 3);
lean_inc(v_numParams_2361_);
v_numFields_2362_ = lean_ctor_get(v_val_2360_, 4);
lean_inc(v_numFields_2362_);
lean_dec(v_val_2360_);
v_nargs_2363_ = l_Lean_Expr_getAppNumArgs(v_self_2354_);
v___x_2364_ = lean_nat_add(v_numParams_2361_, v_numFields_2362_);
lean_dec(v_numFields_2362_);
v_dummy_2365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2363_);
v___x_2366_ = lean_mk_array(v_nargs_2363_, v_dummy_2365_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_sub(v_nargs_2363_, v___x_2367_);
lean_dec(v_nargs_2363_);
lean_inc_ref(v_self_2354_);
v___x_2369_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2354_, v___x_2366_, v___x_2368_);
v___x_2370_ = 0;
v___x_2371_ = lean_box(v___x_2370_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2369_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2364_, v_ctor_2345_, v_numParams_2361_, v___x_2372_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_2364_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2387_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2387_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2387_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_snd_2378_; uint8_t v___x_2379_; 
v_snd_2378_ = lean_ctor_get(v_a_2374_, 1);
v___x_2379_ = lean_unbox(v_snd_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v_a_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v_self_2354_);
v___x_2381_ = v___x_2376_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_self_2354_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
else
{
lean_object* v_fst_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_del_object(v___x_2376_);
v_fst_2383_ = lean_ctor_get(v_a_2374_, 0);
lean_inc(v_fst_2383_);
lean_dec(v_a_2374_);
v___x_2384_ = l_Lean_Expr_getAppFn(v_self_2354_);
lean_dec_ref(v_self_2354_);
v___x_2385_ = l_Lean_mkAppN(v___x_2384_, v_fst_2383_);
lean_dec(v_fst_2383_);
v___x_2386_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_2385_, v_a_2334_);
return v___x_2386_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v_self_2354_);
v_a_2388_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2373_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2373_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v___x_2397_; 
lean_dec(v_a_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v_self_2354_);
v___x_2397_ = v___x_2358_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_self_2354_);
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
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v_self_2354_);
v_a_2400_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2355_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2355_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v_e_2328_);
v_a_2409_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2340_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2340_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2417_, uint8_t v___x_2418_, lean_object* v_a_2419_, lean_object* v_b_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_nat_dec_lt(v_a_2419_, v_upperBound_2417_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
lean_dec(v_a_2419_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_b_2420_);
return v___x_2433_;
}
else
{
lean_object* v_fst_2434_; lean_object* v_snd_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2465_; 
v_fst_2434_ = lean_ctor_get(v_b_2420_, 0);
v_snd_2435_ = lean_ctor_get(v_b_2420_, 1);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_b_2420_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2437_ = v_b_2420_;
v_isShared_2438_ = v_isSharedCheck_2465_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_snd_2435_);
lean_inc(v_fst_2434_);
lean_dec(v_b_2420_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2465_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = l_Lean_instInhabitedExpr;
v___x_2440_ = lean_array_get_borrowed(v___x_2439_, v_fst_2434_, v_a_2419_);
lean_inc(v___x_2440_);
v___x_2441_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2440_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v_a_2444_; uint8_t v___x_2448_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
v___x_2448_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2440_, v_a_2442_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_dec(v_snd_2435_);
v___x_2449_ = lean_array_set(v_fst_2434_, v_a_2419_, v_a_2442_);
v___x_2450_ = lean_box(v___x_2418_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v___x_2450_);
lean_ctor_set(v___x_2437_, 0, v___x_2449_);
v___x_2452_ = v___x_2437_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
v_a_2444_ = v___x_2452_;
goto v___jp_2443_;
}
}
else
{
lean_object* v___x_2455_; 
lean_dec(v_a_2442_);
if (v_isShared_2438_ == 0)
{
v___x_2455_ = v___x_2437_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_fst_2434_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_snd_2435_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
v_a_2444_ = v___x_2455_;
goto v___jp_2443_;
}
}
v___jp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_nat_add(v_a_2419_, v___x_2445_);
lean_dec(v_a_2419_);
v_a_2419_ = v___x_2446_;
v_b_2420_ = v_a_2444_;
goto _start;
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_del_object(v___x_2437_);
lean_dec(v_snd_2435_);
lean_dec(v_fst_2434_);
lean_dec(v_a_2419_);
v_a_2457_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2441_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2441_);
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
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2466_, lean_object* v___x_2467_, lean_object* v_a_2468_, lean_object* v_b_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v___x_15840__boxed_2481_; lean_object* v_res_2482_; 
v___x_15840__boxed_2481_ = lean_unbox(v___x_2467_);
v_res_2482_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2466_, v___x_15840__boxed_2481_, v_a_2468_, v_b_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v_upperBound_2466_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec(v_a_2484_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2496_, uint8_t v___x_2497_, lean_object* v_inst_2498_, lean_object* v_R_2499_, lean_object* v_a_2500_, lean_object* v_b_2501_, lean_object* v_c_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2496_, v___x_2497_, v_a_2500_, v_b_2501_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2515_ = _args[0];
lean_object* v___x_2516_ = _args[1];
lean_object* v_inst_2517_ = _args[2];
lean_object* v_R_2518_ = _args[3];
lean_object* v_a_2519_ = _args[4];
lean_object* v_b_2520_ = _args[5];
lean_object* v_c_2521_ = _args[6];
lean_object* v___y_2522_ = _args[7];
lean_object* v___y_2523_ = _args[8];
lean_object* v___y_2524_ = _args[9];
lean_object* v___y_2525_ = _args[10];
lean_object* v___y_2526_ = _args[11];
lean_object* v___y_2527_ = _args[12];
lean_object* v___y_2528_ = _args[13];
lean_object* v___y_2529_ = _args[14];
lean_object* v___y_2530_ = _args[15];
lean_object* v___y_2531_ = _args[16];
lean_object* v___y_2532_ = _args[17];
_start:
{
uint8_t v___x_16081__boxed_2533_; lean_object* v_res_2534_; 
v___x_16081__boxed_2533_ = lean_unbox(v___x_2516_);
v_res_2534_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2515_, v___x_16081__boxed_2533_, v_inst_2517_, v_R_2518_, v_a_2519_, v_b_2520_, v_c_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec(v_upperBound_2515_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object* v_e_2535_, lean_object* v___y_2536_){
_start:
{
uint8_t v___x_2538_; 
v___x_2538_ = l_Lean_Expr_hasMVar(v_e_2535_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_e_2535_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; lean_object* v_mctx_2541_; lean_object* v___x_2542_; lean_object* v_fst_2543_; lean_object* v_snd_2544_; lean_object* v___x_2545_; lean_object* v_cache_2546_; lean_object* v_zetaDeltaFVarIds_2547_; lean_object* v_postponed_2548_; lean_object* v_diag_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2558_; 
v___x_2540_ = lean_st_ref_get(v___y_2536_);
v_mctx_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc_ref(v_mctx_2541_);
lean_dec(v___x_2540_);
v___x_2542_ = l_Lean_instantiateMVarsCore(v_mctx_2541_, v_e_2535_);
v_fst_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_fst_2543_);
v_snd_2544_ = lean_ctor_get(v___x_2542_, 1);
lean_inc(v_snd_2544_);
lean_dec_ref(v___x_2542_);
v___x_2545_ = lean_st_ref_take(v___y_2536_);
v_cache_2546_ = lean_ctor_get(v___x_2545_, 1);
v_zetaDeltaFVarIds_2547_ = lean_ctor_get(v___x_2545_, 2);
v_postponed_2548_ = lean_ctor_get(v___x_2545_, 3);
v_diag_2549_ = lean_ctor_get(v___x_2545_, 4);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v___x_2545_, 0);
lean_dec(v_unused_2559_);
v___x_2551_ = v___x_2545_;
v_isShared_2552_ = v_isSharedCheck_2558_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_diag_2549_);
lean_inc(v_postponed_2548_);
lean_inc(v_zetaDeltaFVarIds_2547_);
lean_inc(v_cache_2546_);
lean_dec(v___x_2545_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2558_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_snd_2544_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_snd_2544_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_cache_2546_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_zetaDeltaFVarIds_2547_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v_postponed_2548_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v_diag_2549_);
v___x_2554_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_st_ref_set(v___y_2536_, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_fst_2543_);
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object* v_e_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2560_, v___y_2561_);
lean_dec(v___y_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_e_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2564_, v___y_2572_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_e_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_e_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(lean_object* v_k_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2592_);
lean_inc(v___y_2591_);
v___x_2602_ = lean_apply_11(v_k_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, lean_box(0));
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed(lean_object* v_k_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(v_k_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec(v___y_2604_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(lean_object* v_k_2616_, uint8_t v_allowLevelAssignments_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___f_2629_; lean_object* v___x_2630_; 
lean_inc(v___y_2623_);
lean_inc_ref(v___y_2622_);
lean_inc(v___y_2621_);
lean_inc_ref(v___y_2620_);
lean_inc(v___y_2619_);
lean_inc(v___y_2618_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2629_, 0, v_k_2616_);
lean_closure_set(v___f_2629_, 1, v___y_2618_);
lean_closure_set(v___f_2629_, 2, v___y_2619_);
lean_closure_set(v___f_2629_, 3, v___y_2620_);
lean_closure_set(v___f_2629_, 4, v___y_2621_);
lean_closure_set(v___f_2629_, 5, v___y_2622_);
lean_closure_set(v___f_2629_, 6, v___y_2623_);
v___x_2630_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2617_, v___f_2629_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2630_) == 0)
{
return v___x_2630_;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___boxed(lean_object* v_k_2639_, lean_object* v_allowLevelAssignments_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2652_; lean_object* v_res_2653_; 
v_allowLevelAssignments_boxed_2652_ = lean_unbox(v_allowLevelAssignments_2640_);
v_res_2653_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v_k_2639_, v_allowLevelAssignments_boxed_2652_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v___y_2641_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(lean_object* v_00_u03b1_2654_, lean_object* v_k_2655_, uint8_t v_allowLevelAssignments_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v_k_2655_, v_allowLevelAssignments_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_k_2670_, lean_object* v_allowLevelAssignments_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2683_; lean_object* v_res_2684_; 
v_allowLevelAssignments_boxed_2683_ = lean_unbox(v_allowLevelAssignments_2671_);
v_res_2684_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(v_00_u03b1_2669_, v_k_2670_, v_allowLevelAssignments_boxed_2683_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___y_2672_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2685_, lean_object* v_____do__lift_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_options_2698_; uint8_t v_hasTrace_2699_; 
v_options_2698_ = lean_ctor_get(v___y_2695_, 2);
v_hasTrace_2699_ = lean_ctor_get_uint8(v_options_2698_, sizeof(void*)*1);
if (v_hasTrace_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec(v_cls_2685_);
v___x_2700_ = lean_box(v_hasTrace_2699_);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2702_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__5));
v___x_2703_ = l_Lean_Name_append(v___x_2702_, v_cls_2685_);
v___x_2704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2686_, v_options_2698_, v___x_2703_);
lean_dec(v___x_2703_);
v___x_2705_ = lean_box(v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2707_, lean_object* v_____do__lift_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2707_, v_____do__lift_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v_____do__lift_2708_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(lean_object* v_mvarId_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v_mctx_2725_; lean_object* v_decl_2726_; lean_object* v_depth_2727_; lean_object* v_depth_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2724_ = lean_st_ref_get(v___y_2722_);
v_mctx_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc_ref_n(v_mctx_2725_, 2);
lean_dec(v___x_2724_);
v_decl_2726_ = l_Lean_MetavarContext_getDecl(v_mctx_2725_, v_mvarId_2721_);
v_depth_2727_ = lean_ctor_get(v_decl_2726_, 3);
lean_inc(v_depth_2727_);
lean_dec_ref(v_decl_2726_);
v_depth_2728_ = lean_ctor_get(v_mctx_2725_, 0);
lean_inc(v_depth_2728_);
lean_dec_ref(v_mctx_2725_);
v___x_2729_ = lean_nat_dec_eq(v_depth_2727_, v_depth_2728_);
lean_dec(v_depth_2728_);
lean_dec(v_depth_2727_);
v___x_2730_ = lean_box(v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg___boxed(lean_object* v_mvarId_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_2732_, v___y_2733_);
lean_dec(v___y_2733_);
return v_res_2735_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_instMonadEIO(lean_box(0));
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(lean_object* v_msg_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_toApplicative_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2823_; 
v___x_2753_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0);
v___x_2754_ = l_StateRefT_x27_instMonad___redArg(v___x_2753_);
v_toApplicative_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2754_, 1);
lean_dec(v_unused_2824_);
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2823_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_toApplicative_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2823_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_toFunctor_2759_; lean_object* v_toSeq_2760_; lean_object* v_toSeqLeft_2761_; lean_object* v_toSeqRight_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2821_; 
v_toFunctor_2759_ = lean_ctor_get(v_toApplicative_2755_, 0);
v_toSeq_2760_ = lean_ctor_get(v_toApplicative_2755_, 2);
v_toSeqLeft_2761_ = lean_ctor_get(v_toApplicative_2755_, 3);
v_toSeqRight_2762_ = lean_ctor_get(v_toApplicative_2755_, 4);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_toApplicative_2755_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v_toApplicative_2755_, 1);
lean_dec(v_unused_2822_);
v___x_2764_ = v_toApplicative_2755_;
v_isShared_2765_ = v_isSharedCheck_2821_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_toSeqRight_2762_);
lean_inc(v_toSeqLeft_2761_);
lean_inc(v_toSeq_2760_);
lean_inc(v_toFunctor_2759_);
lean_dec(v_toApplicative_2755_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2821_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___f_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___f_2773_; lean_object* v___x_2775_; 
v___f_2766_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__1));
v___f_2767_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__2));
lean_inc_ref(v_toFunctor_2759_);
v___f_2768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2768_, 0, v_toFunctor_2759_);
v___f_2769_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2769_, 0, v_toFunctor_2759_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___f_2768_);
lean_ctor_set(v___x_2770_, 1, v___f_2769_);
v___f_2771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2771_, 0, v_toSeqRight_2762_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeqLeft_2761_);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2773_, 0, v_toSeq_2760_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 4, v___f_2771_);
lean_ctor_set(v___x_2764_, 3, v___f_2772_);
lean_ctor_set(v___x_2764_, 2, v___f_2773_);
lean_ctor_set(v___x_2764_, 1, v___f_2766_);
lean_ctor_set(v___x_2764_, 0, v___x_2770_);
v___x_2775_ = v___x_2764_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___f_2766_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v___f_2773_);
lean_ctor_set(v_reuseFailAlloc_2820_, 3, v___f_2772_);
lean_ctor_set(v_reuseFailAlloc_2820_, 4, v___f_2771_);
v___x_2775_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2777_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___f_2767_);
lean_ctor_set(v___x_2757_, 0, v___x_2775_);
v___x_2777_ = v___x_2757_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___f_2767_);
v___x_2777_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v_toApplicative_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2817_; 
v___x_2778_ = l_StateRefT_x27_instMonad___redArg(v___x_2777_);
v_toApplicative_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2778_, 1);
lean_dec(v_unused_2818_);
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2817_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_toApplicative_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2817_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_toFunctor_2783_; lean_object* v_toSeq_2784_; lean_object* v_toSeqLeft_2785_; lean_object* v_toSeqRight_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2815_; 
v_toFunctor_2783_ = lean_ctor_get(v_toApplicative_2779_, 0);
v_toSeq_2784_ = lean_ctor_get(v_toApplicative_2779_, 2);
v_toSeqLeft_2785_ = lean_ctor_get(v_toApplicative_2779_, 3);
v_toSeqRight_2786_ = lean_ctor_get(v_toApplicative_2779_, 4);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_toApplicative_2779_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v_toApplicative_2779_, 1);
lean_dec(v_unused_2816_);
v___x_2788_ = v_toApplicative_2779_;
v_isShared_2789_ = v_isSharedCheck_2815_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_toSeqRight_2786_);
lean_inc(v_toSeqLeft_2785_);
lean_inc(v_toSeq_2784_);
lean_inc(v_toFunctor_2783_);
lean_dec(v_toApplicative_2779_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2815_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___x_2799_; 
v___f_2790_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__3));
v___f_2791_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__4));
lean_inc_ref(v_toFunctor_2783_);
v___f_2792_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2792_, 0, v_toFunctor_2783_);
v___f_2793_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2793_, 0, v_toFunctor_2783_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___f_2792_);
lean_ctor_set(v___x_2794_, 1, v___f_2793_);
v___f_2795_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2795_, 0, v_toSeqRight_2786_);
v___f_2796_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2796_, 0, v_toSeqLeft_2785_);
v___f_2797_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2797_, 0, v_toSeq_2784_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 4, v___f_2795_);
lean_ctor_set(v___x_2788_, 3, v___f_2796_);
lean_ctor_set(v___x_2788_, 2, v___f_2797_);
lean_ctor_set(v___x_2788_, 1, v___f_2790_);
lean_ctor_set(v___x_2788_, 0, v___x_2794_);
v___x_2799_ = v___x_2788_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v___f_2790_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v___f_2797_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v___f_2796_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v___f_2795_);
v___x_2799_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2801_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 1, v___f_2791_);
lean_ctor_set(v___x_2781_, 0, v___x_2799_);
v___x_2801_ = v___x_2781_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___f_2791_);
v___x_2801_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_109072__overap_2811_; lean_object* v___x_2812_; 
v___x_2802_ = l_StateRefT_x27_instMonad___redArg(v___x_2801_);
v___x_2803_ = l_ReaderT_instMonad___redArg(v___x_2802_);
v___x_2804_ = l_StateRefT_x27_instMonad___redArg(v___x_2803_);
v___x_2805_ = l_ReaderT_instMonad___redArg(v___x_2804_);
v___x_2806_ = l_ReaderT_instMonad___redArg(v___x_2805_);
v___x_2807_ = l_StateRefT_x27_instMonad___redArg(v___x_2806_);
v___x_2808_ = 0;
v___x_2809_ = lean_box(v___x_2808_);
v___x_2810_ = l_instInhabitedOfMonad___redArg(v___x_2807_, v___x_2809_);
v___x_109072__overap_2811_ = lean_panic_fn_borrowed(v___x_2810_, v_msg_2741_);
lean_dec(v___x_2810_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc(v___y_2742_);
v___x_2812_ = lean_apply_11(v___x_109072__overap_2811_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, lean_box(0));
return v___x_2812_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_msg_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(v_msg_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_keys_2838_, lean_object* v_vals_2839_, lean_object* v_i_2840_, lean_object* v_k_2841_){
_start:
{
lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = lean_array_get_size(v_keys_2838_);
v___x_2843_ = lean_nat_dec_lt(v_i_2840_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; 
lean_dec(v_i_2840_);
v___x_2844_ = lean_box(0);
return v___x_2844_;
}
else
{
lean_object* v_k_x27_2845_; uint8_t v___x_2846_; 
v_k_x27_2845_ = lean_array_fget_borrowed(v_keys_2838_, v_i_2840_);
v___x_2846_ = l_Lean_instBEqLevelMVarId_beq(v_k_2841_, v_k_x27_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = lean_nat_add(v_i_2840_, v___x_2847_);
lean_dec(v_i_2840_);
v_i_2840_ = v___x_2848_;
goto _start;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_array_fget_borrowed(v_vals_2839_, v_i_2840_);
lean_dec(v_i_2840_);
lean_inc(v___x_2850_);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_keys_2852_, lean_object* v_vals_2853_, lean_object* v_i_2854_, lean_object* v_k_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_keys_2852_, v_vals_2853_, v_i_2854_, v_k_2855_);
lean_dec(v_k_2855_);
lean_dec_ref(v_vals_2853_);
lean_dec_ref(v_keys_2852_);
return v_res_2856_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; 
v___x_2857_ = ((size_t)5ULL);
v___x_2858_ = ((size_t)1ULL);
v___x_2859_ = lean_usize_shift_left(v___x_2858_, v___x_2857_);
return v___x_2859_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_2860_; size_t v___x_2861_; size_t v___x_2862_; 
v___x_2860_ = ((size_t)1ULL);
v___x_2861_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_2862_ = lean_usize_sub(v___x_2861_, v___x_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(lean_object* v_x_2863_, size_t v_x_2864_, lean_object* v_x_2865_){
_start:
{
if (lean_obj_tag(v_x_2863_) == 0)
{
lean_object* v_es_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2887_; 
v_es_2866_ = lean_ctor_get(v_x_2863_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2863_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2868_ = v_x_2863_;
v_isShared_2869_ = v_isSharedCheck_2887_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_es_2866_);
lean_dec(v_x_2863_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2887_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; size_t v___x_2871_; size_t v___x_2872_; size_t v___x_2873_; lean_object* v_j_2874_; lean_object* v___x_2875_; 
v___x_2870_ = lean_box(2);
v___x_2871_ = ((size_t)5ULL);
v___x_2872_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_2873_ = lean_usize_land(v_x_2864_, v___x_2872_);
v_j_2874_ = lean_usize_to_nat(v___x_2873_);
v___x_2875_ = lean_array_get(v___x_2870_, v_es_2866_, v_j_2874_);
lean_dec(v_j_2874_);
lean_dec_ref(v_es_2866_);
switch(lean_obj_tag(v___x_2875_))
{
case 0:
{
lean_object* v_key_2876_; lean_object* v_val_2877_; uint8_t v___x_2878_; 
v_key_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_key_2876_);
v_val_2877_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_val_2877_);
lean_dec_ref(v___x_2875_);
v___x_2878_ = l_Lean_instBEqLevelMVarId_beq(v_x_2865_, v_key_2876_);
lean_dec(v_key_2876_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_val_2877_);
lean_del_object(v___x_2868_);
v___x_2879_ = lean_box(0);
return v___x_2879_;
}
else
{
lean_object* v___x_2881_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 1);
lean_ctor_set(v___x_2868_, 0, v_val_2877_);
v___x_2881_ = v___x_2868_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_val_2877_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
case 1:
{
lean_object* v_node_2883_; size_t v___x_2884_; 
lean_del_object(v___x_2868_);
v_node_2883_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_node_2883_);
lean_dec_ref(v___x_2875_);
v___x_2884_ = lean_usize_shift_right(v_x_2864_, v___x_2871_);
v_x_2863_ = v_node_2883_;
v_x_2864_ = v___x_2884_;
goto _start;
}
default: 
{
lean_object* v___x_2886_; 
lean_del_object(v___x_2868_);
v___x_2886_ = lean_box(0);
return v___x_2886_;
}
}
}
}
else
{
lean_object* v_ks_2888_; lean_object* v_vs_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_ks_2888_ = lean_ctor_get(v_x_2863_, 0);
lean_inc_ref(v_ks_2888_);
v_vs_2889_ = lean_ctor_get(v_x_2863_, 1);
lean_inc_ref(v_vs_2889_);
lean_dec_ref(v_x_2863_);
v___x_2890_ = lean_unsigned_to_nat(0u);
v___x_2891_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_ks_2888_, v_vs_2889_, v___x_2890_, v_x_2865_);
lean_dec_ref(v_vs_2889_);
lean_dec_ref(v_ks_2888_);
return v___x_2891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
size_t v_x_109931__boxed_2895_; lean_object* v_res_2896_; 
v_x_109931__boxed_2895_ = lean_unbox_usize(v_x_2893_);
lean_dec(v_x_2893_);
v_res_2896_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_2892_, v_x_109931__boxed_2895_, v_x_2894_);
lean_dec(v_x_2894_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
uint64_t v___x_2899_; size_t v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = l_Lean_instHashableLevelMVarId_hash(v_x_2898_);
v___x_2900_ = lean_uint64_to_usize(v___x_2899_);
v___x_2901_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_2897_, v___x_2900_, v_x_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_x_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_x_2902_, v_x_2903_);
lean_dec(v_x_2903_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(lean_object* v_mvarId_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; lean_object* v_mctx_2921_; lean_object* v_levelAssignDepth_2922_; lean_object* v_lDepth_2923_; lean_object* v___x_2924_; 
v___x_2920_ = lean_st_ref_get(v___y_2916_);
v_mctx_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_mctx_2921_);
lean_dec(v___x_2920_);
v_levelAssignDepth_2922_ = lean_ctor_get(v_mctx_2921_, 1);
lean_inc(v_levelAssignDepth_2922_);
v_lDepth_2923_ = lean_ctor_get(v_mctx_2921_, 3);
lean_inc_ref(v_lDepth_2923_);
lean_dec_ref(v_mctx_2921_);
v___x_2924_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_lDepth_2923_, v_mvarId_2908_);
if (lean_obj_tag(v___x_2924_) == 1)
{
lean_object* v_val_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_mvarId_2908_);
v_val_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2934_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_val_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2934_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2929_ = lean_nat_dec_le(v_levelAssignDepth_2922_, v_val_2925_);
lean_dec(v_val_2925_);
lean_dec(v_levelAssignDepth_2922_);
v___x_2930_ = lean_box(v___x_2929_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set_tag(v___x_2927_, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2930_);
v___x_2932_ = v___x_2927_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v___x_2924_);
lean_dec(v_levelAssignDepth_2922_);
v___x_2935_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__0));
v___x_2936_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__1));
v___x_2937_ = lean_unsigned_to_nat(451u);
v___x_2938_ = lean_unsigned_to_nat(14u);
v___x_2939_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__2));
v___x_2940_ = 1;
v___x_2941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2908_, v___x_2940_);
v___x_2942_ = lean_string_append(v___x_2939_, v___x_2941_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = l_mkPanicMessageWithDecl(v___x_2935_, v___x_2936_, v___x_2937_, v___x_2938_, v___x_2942_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(v___x_2943_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___boxed(lean_object* v_mvarId_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(v_mvarId_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object* v_x_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___y_2971_; lean_object* v___y_2972_; uint8_t v_a_2973_; lean_object* v_lvl_u2081_2979_; lean_object* v_lvl_u2082_2980_; 
switch(lean_obj_tag(v_x_2958_))
{
case 1:
{
lean_object* v_a_2987_; uint8_t v___x_2988_; 
v_a_2987_ = lean_ctor_get(v_x_2958_, 0);
lean_inc(v_a_2987_);
lean_dec_ref(v_x_2958_);
v___x_2988_ = l_Lean_Level_hasMVar(v_a_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec(v_a_2987_);
v___x_2989_ = lean_box(v___x_2988_);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
else
{
v_x_2958_ = v_a_2987_;
goto _start;
}
}
case 2:
{
lean_object* v_a_2992_; lean_object* v_a_2993_; 
v_a_2992_ = lean_ctor_get(v_x_2958_, 0);
lean_inc(v_a_2992_);
v_a_2993_ = lean_ctor_get(v_x_2958_, 1);
lean_inc(v_a_2993_);
lean_dec_ref(v_x_2958_);
v_lvl_u2081_2979_ = v_a_2992_;
v_lvl_u2082_2980_ = v_a_2993_;
goto v___jp_2978_;
}
case 3:
{
lean_object* v_a_2994_; lean_object* v_a_2995_; 
v_a_2994_ = lean_ctor_get(v_x_2958_, 0);
lean_inc(v_a_2994_);
v_a_2995_ = lean_ctor_get(v_x_2958_, 1);
lean_inc(v_a_2995_);
lean_dec_ref(v_x_2958_);
v_lvl_u2081_2979_ = v_a_2994_;
v_lvl_u2082_2980_ = v_a_2995_;
goto v___jp_2978_;
}
case 5:
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v_x_2958_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v_x_2958_);
v___x_2997_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(v_a_2996_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2997_;
}
default: 
{
uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v_x_2958_);
v___x_2998_ = 0;
v___x_2999_ = lean_box(v___x_2998_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
v___jp_2970_:
{
if (v_a_2973_ == 0)
{
uint8_t v___x_2974_; 
lean_dec_ref(v___y_2972_);
v___x_2974_ = l_Lean_Level_hasMVar(v___y_2971_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec(v___y_2971_);
v___x_2975_ = lean_box(v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
else
{
v_x_2958_ = v___y_2971_;
goto _start;
}
}
else
{
lean_dec(v___y_2971_);
return v___y_2972_;
}
}
v___jp_2978_:
{
uint8_t v___x_2981_; 
v___x_2981_ = l_Lean_Level_hasMVar(v_lvl_u2081_2979_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_dec(v_lvl_u2081_2979_);
v___x_2982_ = lean_box(v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
v___y_2971_ = v_lvl_u2082_2980_;
v___y_2972_ = v___x_2983_;
v_a_2973_ = v___x_2981_;
goto v___jp_2970_;
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_lvl_u2081_2979_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; uint8_t v___x_2986_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
v___x_2986_ = lean_unbox(v_a_2985_);
lean_dec(v_a_2985_);
v___y_2971_ = v_lvl_u2082_2980_;
v___y_2972_ = v___x_2984_;
v_a_2973_ = v___x_2986_;
goto v___jp_2970_;
}
else
{
lean_dec(v_lvl_u2082_2980_);
return v___x_2984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object* v_x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_x_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec(v___y_3002_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(lean_object* v_x_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
if (lean_obj_tag(v_x_3014_) == 0)
{
uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = 0;
v___x_3027_ = lean_box(v___x_3026_);
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
else
{
lean_object* v_head_3029_; lean_object* v_tail_3030_; lean_object* v___x_3031_; 
v_head_3029_ = lean_ctor_get(v_x_3014_, 0);
lean_inc(v_head_3029_);
v_tail_3030_ = lean_ctor_get(v_x_3014_, 1);
lean_inc(v_tail_3030_);
lean_dec_ref(v_x_3014_);
v___x_3031_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_head_3029_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; uint8_t v___x_3033_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
v___x_3033_ = lean_unbox(v_a_3032_);
lean_dec(v_a_3032_);
if (v___x_3033_ == 0)
{
lean_dec_ref(v___x_3031_);
v_x_3014_ = v_tail_3030_;
goto _start;
}
else
{
lean_dec(v_tail_3030_);
return v___x_3031_;
}
}
else
{
lean_dec(v_tail_3030_);
return v___x_3031_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4___boxed(lean_object* v_x_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(v_x_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec(v___y_3036_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_x_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___y_3061_; lean_object* v___y_3062_; uint8_t v_a_3063_; lean_object* v_d_3069_; lean_object* v_b_3070_; 
switch(lean_obj_tag(v_x_3048_))
{
case 2:
{
lean_object* v_mvarId_3077_; lean_object* v___x_3078_; 
v_mvarId_3077_ = lean_ctor_get(v_x_3048_, 0);
lean_inc(v_mvarId_3077_);
lean_dec_ref(v_x_3048_);
v___x_3078_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_3077_, v___y_3056_);
return v___x_3078_;
}
case 3:
{
lean_object* v_u_3079_; lean_object* v___x_3080_; 
v_u_3079_ = lean_ctor_get(v_x_3048_, 0);
lean_inc(v_u_3079_);
lean_dec_ref(v_x_3048_);
v___x_3080_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_u_3079_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
return v___x_3080_;
}
case 4:
{
lean_object* v_us_3081_; lean_object* v___x_3082_; 
v_us_3081_ = lean_ctor_get(v_x_3048_, 1);
lean_inc(v_us_3081_);
lean_dec_ref(v_x_3048_);
v___x_3082_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(v_us_3081_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
return v___x_3082_;
}
case 5:
{
lean_object* v_fn_3083_; lean_object* v_arg_3084_; lean_object* v___y_3086_; uint8_t v_a_3087_; uint8_t v___x_3092_; 
v_fn_3083_ = lean_ctor_get(v_x_3048_, 0);
lean_inc_ref(v_fn_3083_);
v_arg_3084_ = lean_ctor_get(v_x_3048_, 1);
lean_inc_ref(v_arg_3084_);
lean_dec_ref(v_x_3048_);
v___x_3092_ = l_Lean_Expr_hasMVar(v_fn_3083_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref(v_fn_3083_);
v___x_3093_ = lean_box(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
v___y_3086_ = v___x_3094_;
v_a_3087_ = v___x_3092_;
goto v___jp_3085_;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_fn_3083_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; uint8_t v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
v___x_3097_ = lean_unbox(v_a_3096_);
lean_dec(v_a_3096_);
v___y_3086_ = v___x_3095_;
v_a_3087_ = v___x_3097_;
goto v___jp_3085_;
}
else
{
lean_dec_ref(v_arg_3084_);
return v___x_3095_;
}
}
v___jp_3085_:
{
if (v_a_3087_ == 0)
{
uint8_t v___x_3088_; 
lean_dec_ref(v___y_3086_);
v___x_3088_ = l_Lean_Expr_hasMVar(v_arg_3084_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec_ref(v_arg_3084_);
v___x_3089_ = lean_box(v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
else
{
v_x_3048_ = v_arg_3084_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_3084_);
return v___y_3086_;
}
}
}
case 6:
{
lean_object* v_binderType_3098_; lean_object* v_body_3099_; 
v_binderType_3098_ = lean_ctor_get(v_x_3048_, 1);
lean_inc_ref(v_binderType_3098_);
v_body_3099_ = lean_ctor_get(v_x_3048_, 2);
lean_inc_ref(v_body_3099_);
lean_dec_ref(v_x_3048_);
v_d_3069_ = v_binderType_3098_;
v_b_3070_ = v_body_3099_;
goto v___jp_3068_;
}
case 7:
{
lean_object* v_binderType_3100_; lean_object* v_body_3101_; 
v_binderType_3100_ = lean_ctor_get(v_x_3048_, 1);
lean_inc_ref(v_binderType_3100_);
v_body_3101_ = lean_ctor_get(v_x_3048_, 2);
lean_inc_ref(v_body_3101_);
lean_dec_ref(v_x_3048_);
v_d_3069_ = v_binderType_3100_;
v_b_3070_ = v_body_3101_;
goto v___jp_3068_;
}
case 8:
{
lean_object* v_type_3102_; lean_object* v_value_3103_; lean_object* v_body_3104_; lean_object* v___y_3106_; uint8_t v_a_3107_; lean_object* v___y_3113_; uint8_t v_a_3114_; uint8_t v___x_3121_; 
v_type_3102_ = lean_ctor_get(v_x_3048_, 1);
lean_inc_ref(v_type_3102_);
v_value_3103_ = lean_ctor_get(v_x_3048_, 2);
lean_inc_ref(v_value_3103_);
v_body_3104_ = lean_ctor_get(v_x_3048_, 3);
lean_inc_ref(v_body_3104_);
lean_dec_ref(v_x_3048_);
v___x_3121_ = l_Lean_Expr_hasMVar(v_type_3102_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_type_3102_);
v___x_3122_ = lean_box(v___x_3121_);
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
v___y_3113_ = v___x_3123_;
v_a_3114_ = v___x_3121_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_type_3102_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; uint8_t v___x_3126_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
v___x_3126_ = lean_unbox(v_a_3125_);
lean_dec(v_a_3125_);
v___y_3113_ = v___x_3124_;
v_a_3114_ = v___x_3126_;
goto v___jp_3112_;
}
else
{
lean_dec_ref(v_body_3104_);
lean_dec_ref(v_value_3103_);
return v___x_3124_;
}
}
v___jp_3105_:
{
if (v_a_3107_ == 0)
{
uint8_t v___x_3108_; 
lean_dec_ref(v___y_3106_);
v___x_3108_ = l_Lean_Expr_hasMVar(v_body_3104_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec_ref(v_body_3104_);
v___x_3109_ = lean_box(v___x_3108_);
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
return v___x_3110_;
}
else
{
v_x_3048_ = v_body_3104_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_3104_);
return v___y_3106_;
}
}
v___jp_3112_:
{
if (v_a_3114_ == 0)
{
uint8_t v___x_3115_; 
lean_dec_ref(v___y_3113_);
v___x_3115_ = l_Lean_Expr_hasMVar(v_value_3103_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v_value_3103_);
v___x_3116_ = lean_box(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
v___y_3106_ = v___x_3117_;
v_a_3107_ = v___x_3115_;
goto v___jp_3105_;
}
else
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_value_3103_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; uint8_t v___x_3120_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
v___x_3120_ = lean_unbox(v_a_3119_);
lean_dec(v_a_3119_);
v___y_3106_ = v___x_3118_;
v_a_3107_ = v___x_3120_;
goto v___jp_3105_;
}
else
{
lean_dec_ref(v_body_3104_);
return v___x_3118_;
}
}
}
else
{
lean_dec_ref(v_body_3104_);
lean_dec_ref(v_value_3103_);
return v___y_3113_;
}
}
}
case 10:
{
lean_object* v_expr_3127_; uint8_t v___x_3128_; 
v_expr_3127_ = lean_ctor_get(v_x_3048_, 1);
lean_inc_ref(v_expr_3127_);
lean_dec_ref(v_x_3048_);
v___x_3128_ = l_Lean_Expr_hasMVar(v_expr_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v_expr_3127_);
v___x_3129_ = lean_box(v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
else
{
v_x_3048_ = v_expr_3127_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_3132_; uint8_t v___x_3133_; 
v_struct_3132_ = lean_ctor_get(v_x_3048_, 2);
lean_inc_ref(v_struct_3132_);
lean_dec_ref(v_x_3048_);
v___x_3133_ = l_Lean_Expr_hasMVar(v_struct_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_struct_3132_);
v___x_3134_ = lean_box(v___x_3133_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
else
{
v_x_3048_ = v_struct_3132_;
goto _start;
}
}
default: 
{
uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec_ref(v_x_3048_);
v___x_3137_ = 0;
v___x_3138_ = lean_box(v___x_3137_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
v___jp_3060_:
{
if (v_a_3063_ == 0)
{
uint8_t v___x_3064_; 
lean_dec_ref(v___y_3062_);
v___x_3064_ = l_Lean_Expr_hasMVar(v___y_3061_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec_ref(v___y_3061_);
v___x_3065_ = lean_box(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
else
{
v_x_3048_ = v___y_3061_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_3061_);
return v___y_3062_;
}
}
v___jp_3068_:
{
uint8_t v___x_3071_; 
v___x_3071_ = l_Lean_Expr_hasMVar(v_d_3069_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v_d_3069_);
v___x_3072_ = lean_box(v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___y_3061_ = v_b_3070_;
v___y_3062_ = v___x_3073_;
v_a_3063_ = v___x_3071_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_d_3069_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; uint8_t v___x_3076_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
v___x_3076_ = lean_unbox(v_a_3075_);
lean_dec(v_a_3075_);
v___y_3061_ = v_b_3070_;
v___y_3062_ = v___x_3074_;
v_a_3063_ = v___x_3076_;
goto v___jp_3060_;
}
else
{
lean_dec_ref(v_b_3070_);
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_x_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_x_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
return v_res_3152_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3(void){
_start:
{
lean_object* v_cls_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_cls_3161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_3162_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__5));
v___x_3163_ = l_Lean_Name_append(v___x_3162_, v_cls_3161_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4));
v___x_3166_ = l_Lean_stringToMessageData(v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_as_3167_, size_t v_sz_3168_, size_t v_i_3169_, lean_object* v_b_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_a_3183_; uint8_t v___x_3187_; 
v___x_3187_ = lean_usize_dec_lt(v_i_3169_, v_sz_3168_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_b_3170_);
return v___x_3188_;
}
else
{
lean_object* v_snd_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3376_; 
v_snd_3189_ = lean_ctor_get(v_b_3170_, 1);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_b_3170_);
if (v_isSharedCheck_3376_ == 0)
{
lean_object* v_unused_3377_; 
v_unused_3377_ = lean_ctor_get(v_b_3170_, 0);
lean_dec(v_unused_3377_);
v___x_3191_ = v_b_3170_;
v_isShared_3192_ = v_isSharedCheck_3376_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_snd_3189_);
lean_dec(v_b_3170_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3376_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v_array_3193_; lean_object* v_start_3194_; lean_object* v_stop_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_array_3193_ = lean_ctor_get(v_snd_3189_, 0);
v_start_3194_ = lean_ctor_get(v_snd_3189_, 1);
v_stop_3195_ = lean_ctor_get(v_snd_3189_, 2);
v___x_3196_ = lean_box(0);
v___x_3197_ = lean_nat_dec_lt(v_start_3194_, v_stop_3195_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3199_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3196_);
v___x_3199_ = v___x_3191_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_snd_3189_);
v___x_3199_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
return v___x_3200_;
}
}
else
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3372_; 
lean_inc(v_stop_3195_);
lean_inc(v_start_3194_);
lean_inc_ref(v_array_3193_);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_snd_3189_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; lean_object* v_unused_3374_; lean_object* v_unused_3375_; 
v_unused_3373_ = lean_ctor_get(v_snd_3189_, 2);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_snd_3189_, 1);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v_snd_3189_, 0);
lean_dec(v_unused_3375_);
v___x_3203_ = v_snd_3189_;
v_isShared_3204_ = v_isSharedCheck_3372_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v_snd_3189_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3372_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3205_ = lean_array_fget(v_array_3193_, v_start_3194_);
v___x_3206_ = lean_unsigned_to_nat(1u);
v___x_3207_ = lean_nat_add(v_start_3194_, v___x_3206_);
lean_dec(v_start_3194_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 1, v___x_3207_);
v___x_3209_ = v___x_3203_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_array_3193_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_stop_3195_);
v___x_3209_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
uint8_t v___x_3210_; 
v___x_3210_ = lean_unbox(v___x_3205_);
lean_dec(v___x_3205_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3212_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3209_);
lean_ctor_set(v___x_3191_, 0, v___x_3196_);
v___x_3212_ = v___x_3191_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3209_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
v_a_3183_ = v___x_3212_;
goto v___jp_3182_;
}
}
else
{
lean_object* v_a_3214_; lean_object* v_____x_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___x_3252_; 
v_a_3214_ = lean_array_uget_borrowed(v_as_3167_, v_i_3169_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v_a_3214_);
v___x_3252_ = lean_infer_type(v_a_3214_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3362_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3362_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3362_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; 
v___x_3257_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3253_);
if (lean_obj_tag(v___x_3257_) == 1)
{
lean_object* v_val_3258_; lean_object* v_snd_3259_; lean_object* v_fst_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3356_; 
lean_del_object(v___x_3255_);
v_val_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_val_3258_);
lean_dec_ref(v___x_3257_);
v_snd_3259_ = lean_ctor_get(v_val_3258_, 1);
v_fst_3260_ = lean_ctor_get(v_val_3258_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_val_3258_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3262_ = v_val_3258_;
v_isShared_3263_ = v_isSharedCheck_3356_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_snd_3259_);
lean_inc(v_fst_3260_);
lean_dec(v_val_3258_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3356_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3355_; 
v_fst_3264_ = lean_ctor_get(v_snd_3259_, 0);
v_snd_3265_ = lean_ctor_get(v_snd_3259_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_snd_3259_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3267_ = v_snd_3259_;
v_isShared_3268_ = v_isSharedCheck_3355_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snd_3265_);
lean_inc(v_fst_3264_);
lean_dec(v_snd_3259_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3355_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; 
lean_inc(v_fst_3264_);
v___x_3269_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3264_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v_options_3325_; uint8_t v_hasTrace_3326_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v_options_3325_ = lean_ctor_get(v___y_3179_, 2);
v_hasTrace_3326_ = lean_ctor_get_uint8(v_options_3325_, sizeof(void*)*1);
if (v_hasTrace_3326_ == 0)
{
lean_del_object(v___x_3262_);
v___y_3272_ = v___y_3171_;
v___y_3273_ = v___y_3172_;
v___y_3274_ = v___y_3173_;
v___y_3275_ = v___y_3174_;
v___y_3276_ = v___y_3175_;
v___y_3277_ = v___y_3176_;
v___y_3278_ = v___y_3177_;
v___y_3279_ = v___y_3178_;
v___y_3280_ = v___y_3179_;
v___y_3281_ = v___y_3180_;
goto v___jp_3271_;
}
else
{
lean_object* v_inheritedTraceOptions_3327_; lean_object* v_cls_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v_inheritedTraceOptions_3327_ = lean_ctor_get(v___y_3179_, 13);
v_cls_3328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_3329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3);
v___x_3330_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3327_, v_options_3325_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_del_object(v___x_3262_);
v___y_3272_ = v___y_3171_;
v___y_3273_ = v___y_3172_;
v___y_3274_ = v___y_3173_;
v___y_3275_ = v___y_3174_;
v___y_3276_ = v___y_3175_;
v___y_3277_ = v___y_3176_;
v___y_3278_ = v___y_3177_;
v___y_3279_ = v___y_3178_;
v___y_3280_ = v___y_3179_;
v___y_3281_ = v___y_3180_;
goto v___jp_3271_;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_inc(v_a_3270_);
v___x_3331_ = l_Lean_MessageData_ofExpr(v_a_3270_);
v___x_3332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5);
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 7);
lean_ctor_set(v___x_3262_, 1, v___x_3332_);
lean_ctor_set(v___x_3262_, 0, v___x_3331_);
v___x_3334_ = v___x_3262_;
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
lean_inc(v_snd_3265_);
v___x_3335_ = l_Lean_MessageData_ofExpr(v_snd_3265_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3328_, v___x_3336_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_dec_ref(v___x_3337_);
v___y_3272_ = v___y_3171_;
v___y_3273_ = v___y_3172_;
v___y_3274_ = v___y_3173_;
v___y_3275_ = v___y_3174_;
v___y_3276_ = v___y_3175_;
v___y_3277_ = v___y_3176_;
v___y_3278_ = v___y_3177_;
v___y_3279_ = v___y_3178_;
v___y_3280_ = v___y_3179_;
v___y_3281_ = v___y_3180_;
goto v___jp_3271_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3270_);
lean_del_object(v___x_3267_);
lean_dec(v_snd_3265_);
lean_dec(v_fst_3264_);
lean_dec(v_fst_3260_);
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
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
}
v___jp_3271_:
{
lean_object* v___x_3282_; 
lean_inc(v_a_3270_);
v___x_3282_ = l_Lean_Meta_isDefEqD(v_a_3270_, v_snd_3265_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3316_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3316_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3316_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
uint8_t v___x_3287_; 
v___x_3287_ = lean_unbox(v_a_3283_);
lean_dec(v_a_3283_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
lean_dec(v_a_3270_);
lean_dec(v_fst_3264_);
lean_dec(v_fst_3260_);
lean_del_object(v___x_3191_);
v___x_3288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 1, v___x_3209_);
lean_ctor_set(v___x_3267_, 0, v___x_3288_);
v___x_3290_ = v___x_3267_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___x_3209_);
v___x_3290_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3292_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3290_);
v___x_3292_ = v___x_3285_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
else
{
lean_del_object(v___x_3285_);
lean_del_object(v___x_3267_);
if (lean_obj_tag(v_fst_3260_) == 0)
{
uint8_t v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = 0;
v___x_3296_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3264_, v_a_3270_, v___x_3295_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref(v___x_3296_);
v_____x_3216_ = v_a_3297_;
v___y_3217_ = v___y_3278_;
v___y_3218_ = v___y_3279_;
v___y_3219_ = v___y_3280_;
v___y_3220_ = v___y_3281_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
v_a_3298_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3296_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3296_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v___x_3306_; 
lean_dec_ref(v_fst_3260_);
v___x_3306_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3264_, v_a_3270_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref(v___x_3306_);
v_____x_3216_ = v_a_3307_;
v___y_3217_ = v___y_3278_;
v___y_3218_ = v___y_3279_;
v___y_3219_ = v___y_3280_;
v___y_3220_ = v___y_3281_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
v_a_3308_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3306_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3306_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_a_3270_);
lean_del_object(v___x_3267_);
lean_dec(v_fst_3264_);
lean_dec(v_fst_3260_);
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
v_a_3317_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3282_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3282_);
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
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_del_object(v___x_3267_);
lean_dec(v_snd_3265_);
lean_dec(v_fst_3264_);
lean_del_object(v___x_3262_);
lean_dec(v_fst_3260_);
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
v_a_3347_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3269_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3269_);
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
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
lean_dec(v___x_3257_);
lean_del_object(v___x_3191_);
v___x_3357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___x_3209_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3358_);
v___x_3360_ = v___x_3255_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
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
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
v_a_3363_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3252_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3252_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
v___jp_3215_:
{
if (lean_obj_tag(v_____x_3216_) == 1)
{
lean_object* v_val_3221_; lean_object* v___x_3222_; 
v_val_3221_ = lean_ctor_get(v_____x_3216_, 0);
lean_inc(v_val_3221_);
lean_dec_ref(v_____x_3216_);
lean_inc(v_a_3214_);
v___x_3222_ = l_Lean_Meta_isExprDefEq(v_a_3214_, v_val_3221_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3238_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3238_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3238_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_unbox(v_a_3223_);
lean_dec(v_a_3223_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3209_);
lean_ctor_set(v___x_3191_, 0, v___x_3228_);
v___x_3230_ = v___x_3191_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3209_);
v___x_3230_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3232_; 
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3230_);
v___x_3232_ = v___x_3225_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v___x_3236_; 
lean_del_object(v___x_3225_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3209_);
lean_ctor_set(v___x_3191_, 0, v___x_3196_);
v___x_3236_ = v___x_3191_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3209_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
v_a_3183_ = v___x_3236_;
goto v___jp_3182_;
}
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec_ref(v___x_3209_);
lean_del_object(v___x_3191_);
v_a_3239_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3222_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3222_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
lean_dec(v_____x_3216_);
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3209_);
lean_ctor_set(v___x_3191_, 0, v___x_3247_);
v___x_3249_ = v___x_3191_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3209_);
v___x_3249_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
}
}
}
}
}
}
}
v___jp_3182_:
{
size_t v___x_3184_; size_t v___x_3185_; 
v___x_3184_ = ((size_t)1ULL);
v___x_3185_ = lean_usize_add(v_i_3169_, v___x_3184_);
v_i_3169_ = v___x_3185_;
v_b_3170_ = v_a_3183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_as_3378_, lean_object* v_sz_3379_, lean_object* v_i_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
size_t v_sz_boxed_3393_; size_t v_i_boxed_3394_; lean_object* v_res_3395_; 
v_sz_boxed_3393_ = lean_unbox_usize(v_sz_3379_);
lean_dec(v_sz_3379_);
v_i_boxed_3394_ = lean_unbox_usize(v_i_3380_);
lean_dec(v_i_3380_);
v_res_3395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_as_3378_, v_sz_boxed_3393_, v_i_boxed_3394_, v_b_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v_as_3378_);
return v_res_3395_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3399_, uint8_t v___x_3400_, lean_object* v_e_3401_, lean_object* v___f_3402_, lean_object* v_cls_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; 
lean_inc_ref(v_arg_3399_);
v___x_3415_ = l_Lean_Meta_forallMetaTelescope(v_arg_3399_, v___x_3400_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v_fst_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3534_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref(v___x_3415_);
v_fst_3417_ = lean_ctor_get(v_a_3416_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v_a_3416_, 1);
lean_dec(v_unused_3535_);
v___x_3419_ = v_a_3416_;
v_isShared_3420_ = v_isSharedCheck_3534_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_fst_3417_);
lean_dec(v_a_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3534_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3421_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3399_);
lean_dec_ref(v_arg_3399_);
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_array_get_size(v___x_3421_);
v___x_3424_ = l_Array_toSubarray___redArg(v___x_3421_, v___x_3422_, v___x_3423_);
v___x_3425_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 1, v___x_3424_);
lean_ctor_set(v___x_3419_, 0, v___x_3425_);
v___x_3427_ = v___x_3419_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3424_);
v___x_3427_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
size_t v_sz_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
v_sz_3428_ = lean_array_size(v_fst_3417_);
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_fst_3417_, v_sz_3428_, v___x_3429_, v___x_3427_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3524_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3524_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3524_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_fst_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3522_; 
v_fst_3435_ = lean_ctor_get(v_a_3431_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_a_3431_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; 
v_unused_3523_ = lean_ctor_get(v_a_3431_, 1);
lean_dec(v_unused_3523_);
v___x_3437_ = v_a_3431_;
v_isShared_3438_ = v_isSharedCheck_3522_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_fst_3435_);
lean_dec(v_a_3431_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3522_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
if (lean_obj_tag(v_fst_3435_) == 0)
{
lean_object* v___x_3439_; 
lean_del_object(v___x_3433_);
lean_inc_ref(v_e_3401_);
v___x_3439_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3401_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3509_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref(v___x_3439_);
v___x_3441_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3401_, v_a_3440_);
v___x_3442_ = l_Lean_mkAppN(v___x_3441_, v_fst_3417_);
lean_dec(v_fst_3417_);
v___x_3443_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v___x_3442_, v___y_3411_);
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3509_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3509_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3453_; 
lean_inc(v_a_3444_);
v___x_3453_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_a_3444_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3500_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3500_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3500_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_unbox(v_a_3454_);
lean_dec(v_a_3454_);
if (v___x_3458_ == 0)
{
lean_object* v_inheritedTraceOptions_3459_; lean_object* v___x_3460_; 
lean_del_object(v___x_3456_);
v_inheritedTraceOptions_3459_ = lean_ctor_get(v___y_3412_, 13);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3410_);
lean_inc(v___y_3409_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3407_);
lean_inc_ref(v___y_3406_);
lean_inc(v___y_3405_);
lean_inc(v___y_3404_);
lean_inc_ref(v_inheritedTraceOptions_3459_);
v___x_3460_ = lean_apply_12(v___f_3402_, v_inheritedTraceOptions_3459_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, lean_box(0));
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; uint8_t v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref(v___x_3460_);
v___x_3462_ = lean_unbox(v_a_3461_);
lean_dec(v_a_3461_);
if (v___x_3462_ == 0)
{
lean_del_object(v___x_3437_);
lean_dec(v_cls_3403_);
goto v___jp_3448_;
}
else
{
lean_object* v___x_3463_; 
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3410_);
lean_inc(v_a_3444_);
v___x_3463_ = lean_infer_type(v_a_3444_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3463_);
lean_inc(v_a_3444_);
v___x_3465_ = l_Lean_MessageData_ofExpr(v_a_3444_);
v___x_3466_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 7);
lean_ctor_set(v___x_3437_, 1, v___x_3466_);
lean_ctor_set(v___x_3437_, 0, v___x_3465_);
v___x_3468_ = v___x_3437_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = l_Lean_MessageData_ofExpr(v_a_3464_);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3403_, v___x_3470_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_dec_ref(v___x_3471_);
goto v___jp_3448_;
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_del_object(v___x_3446_);
lean_dec(v_a_3444_);
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_del_object(v___x_3446_);
lean_dec(v_a_3444_);
lean_del_object(v___x_3437_);
lean_dec(v_cls_3403_);
v_a_3481_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3463_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3463_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_del_object(v___x_3446_);
lean_dec(v_a_3444_);
lean_del_object(v___x_3437_);
lean_dec(v_cls_3403_);
v_a_3489_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3460_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3460_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v___x_3498_; 
lean_del_object(v___x_3446_);
lean_dec(v_a_3444_);
lean_del_object(v___x_3437_);
lean_dec(v_cls_3403_);
lean_dec_ref(v___f_3402_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3425_);
v___x_3498_ = v___x_3456_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3425_);
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
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_del_object(v___x_3446_);
lean_dec(v_a_3444_);
lean_del_object(v___x_3437_);
lean_dec(v_cls_3403_);
lean_dec_ref(v___f_3402_);
v_a_3501_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3453_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3453_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
v___jp_3448_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3444_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3449_);
v___x_3451_ = v___x_3446_;
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
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_del_object(v___x_3437_);
lean_dec(v_fst_3417_);
lean_dec(v_cls_3403_);
lean_dec_ref(v___f_3402_);
lean_dec_ref(v_e_3401_);
v_a_3510_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3439_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3439_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_val_3518_; lean_object* v___x_3520_; 
lean_del_object(v___x_3437_);
lean_dec(v_fst_3417_);
lean_dec(v_cls_3403_);
lean_dec_ref(v___f_3402_);
lean_dec_ref(v_e_3401_);
v_val_3518_ = lean_ctor_get(v_fst_3435_, 0);
lean_inc(v_val_3518_);
lean_dec_ref(v_fst_3435_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v_val_3518_);
v___x_3520_ = v___x_3433_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_val_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_fst_3417_);
lean_dec(v_cls_3403_);
lean_dec_ref(v___f_3402_);
lean_dec_ref(v_e_3401_);
v_a_3525_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3430_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3430_);
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
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_cls_3403_);
lean_dec_ref(v___f_3402_);
lean_dec_ref(v_e_3401_);
lean_dec_ref(v_arg_3399_);
v_a_3536_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3415_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3415_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3544_, lean_object* v___x_3545_, lean_object* v_e_3546_, lean_object* v___f_3547_, lean_object* v_cls_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
uint8_t v___x_110921__boxed_3560_; lean_object* v_res_3561_; 
v___x_110921__boxed_3560_ = lean_unbox(v___x_3545_);
v_res_3561_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3544_, v___x_110921__boxed_3560_, v_e_3546_, v___f_3547_, v_cls_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec(v___y_3549_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_inheritedTraceOptions_3579_; lean_object* v_cls_3580_; lean_object* v___f_3581_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___x_3633_; lean_object* v_a_3634_; uint8_t v___x_3635_; 
v_inheritedTraceOptions_3579_ = lean_ctor_get(v_a_3573_, 13);
v_cls_3580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___f_3581_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3633_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3580_, v_inheritedTraceOptions_3579_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
v___x_3635_ = lean_unbox(v_a_3634_);
lean_dec(v_a_3634_);
if (v___x_3635_ == 0)
{
v___y_3583_ = v_a_3565_;
v___y_3584_ = v_a_3566_;
v___y_3585_ = v_a_3567_;
v___y_3586_ = v_a_3568_;
v___y_3587_ = v_a_3569_;
v___y_3588_ = v_a_3570_;
v___y_3589_ = v_a_3571_;
v___y_3590_ = v_a_3572_;
v___y_3591_ = v_a_3573_;
v___y_3592_ = v_a_3574_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Meta_Grind_updateLastTag(v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_dec_ref(v___x_3636_);
lean_inc_ref(v_e_3564_);
v___x_3637_ = l_Lean_MessageData_ofExpr(v_e_3564_);
v___x_3638_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3580_, v___x_3637_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_dec_ref(v___x_3638_);
v___y_3583_ = v_a_3565_;
v___y_3584_ = v_a_3566_;
v___y_3585_ = v_a_3567_;
v___y_3586_ = v_a_3568_;
v___y_3587_ = v_a_3569_;
v___y_3588_ = v_a_3570_;
v___y_3589_ = v_a_3571_;
v___y_3590_ = v_a_3572_;
v___y_3591_ = v_a_3573_;
v___y_3592_ = v_a_3574_;
goto v___jp_3582_;
}
else
{
lean_dec_ref(v_e_3564_);
return v___x_3638_;
}
}
else
{
lean_dec_ref(v_e_3564_);
return v___x_3636_;
}
}
v___jp_3576_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
v___jp_3582_:
{
lean_object* v___x_3593_; 
lean_inc_ref(v_e_3564_);
v___x_3593_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3564_, v___y_3590_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = l_Lean_Expr_cleanupAnnotations(v_a_3594_);
v___x_3596_ = l_Lean_Expr_isApp(v___x_3595_);
if (v___x_3596_ == 0)
{
lean_dec_ref(v___x_3595_);
lean_dec_ref(v_e_3564_);
goto v___jp_3576_;
}
else
{
lean_object* v_arg_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v_arg_3597_ = lean_ctor_get(v___x_3595_, 1);
lean_inc_ref(v_arg_3597_);
v___x_3598_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3595_);
v___x_3599_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3600_ = l_Lean_Expr_isConstOf(v___x_3598_, v___x_3599_);
lean_dec_ref(v___x_3598_);
if (v___x_3600_ == 0)
{
lean_dec_ref(v_arg_3597_);
lean_dec_ref(v_e_3564_);
goto v___jp_3576_;
}
else
{
uint8_t v___x_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; 
v___x_3601_ = 0;
v___x_3602_ = lean_box(v___x_3601_);
v___f_3603_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3603_, 0, v_arg_3597_);
lean_closure_set(v___f_3603_, 1, v___x_3602_);
lean_closure_set(v___f_3603_, 2, v_e_3564_);
lean_closure_set(v___f_3603_, 3, v___f_3581_);
lean_closure_set(v___f_3603_, 4, v_cls_3580_);
v___x_3604_ = 0;
v___x_3605_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v___f_3603_, v___x_3604_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3616_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3616_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3616_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
if (lean_obj_tag(v_a_3606_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3608_);
v_val_3610_ = lean_ctor_get(v_a_3606_, 0);
lean_inc(v_val_3610_);
lean_dec_ref(v_a_3606_);
v___x_3611_ = l_Lean_Meta_Grind_closeGoal(v_val_3610_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_dec(v_a_3606_);
v___x_3612_ = lean_box(0);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3612_);
v___x_3614_ = v___x_3608_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_a_3617_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3605_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3605_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
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
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v_e_3564_);
v_a_3625_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3593_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3593_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec(v_a_3640_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(lean_object* v_mvarId_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_3652_, v___y_3660_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___boxed(lean_object* v_mvarId_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(v_mvarId_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec(v___y_3666_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3678_, lean_object* v_x_3679_, lean_object* v_x_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_x_3679_, v_x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(v_00_u03b2_3682_, v_x_3683_, v_x_3684_);
lean_dec(v_x_3684_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_3686_, lean_object* v_x_3687_, size_t v_x_3688_, lean_object* v_x_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_3687_, v_x_3688_, v_x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3691_, lean_object* v_x_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
size_t v_x_111422__boxed_3695_; lean_object* v_res_3696_; 
v_x_111422__boxed_3695_ = lean_unbox_usize(v_x_3693_);
lean_dec(v_x_3693_);
v_res_3696_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(v_00_u03b2_3691_, v_x_3692_, v_x_111422__boxed_3695_, v_x_3694_);
lean_dec(v_x_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_3697_, lean_object* v_keys_3698_, lean_object* v_vals_3699_, lean_object* v_heq_3700_, lean_object* v_i_3701_, lean_object* v_k_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_keys_3698_, v_vals_3699_, v_i_3701_, v_k_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_3704_, lean_object* v_keys_3705_, lean_object* v_vals_3706_, lean_object* v_heq_3707_, lean_object* v_i_3708_, lean_object* v_k_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_3704_, v_keys_3705_, v_vals_3706_, v_heq_3707_, v_i_3708_, v_k_3709_);
lean_dec(v_k_3709_);
lean_dec_ref(v_vals_3706_);
lean_dec_ref(v_keys_3705_);
return v_res_3710_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
return v___x_3713_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v_options_3743_; lean_object* v_inheritedTraceOptions_3744_; uint8_t v_hasTrace_3745_; lean_object* v_cls_3746_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; 
v_options_3743_ = lean_ctor_get(v_a_3726_, 2);
v_inheritedTraceOptions_3744_ = lean_ctor_get(v_a_3726_, 13);
v_hasTrace_3745_ = lean_ctor_get_uint8(v_options_3743_, sizeof(void*)*1);
v_cls_3746_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__3));
if (v_hasTrace_3745_ == 0)
{
v___y_3748_ = v_a_3718_;
v___y_3749_ = v_a_3719_;
v___y_3750_ = v_a_3720_;
v___y_3751_ = v_a_3721_;
v___y_3752_ = v_a_3722_;
v___y_3753_ = v_a_3723_;
v___y_3754_ = v_a_3724_;
v___y_3755_ = v_a_3725_;
v___y_3756_ = v_a_3726_;
v___y_3757_ = v_a_3727_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6);
v___x_3854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3744_, v_options_3743_, v___x_3853_);
if (v___x_3854_ == 0)
{
v___y_3748_ = v_a_3718_;
v___y_3749_ = v_a_3719_;
v___y_3750_ = v_a_3720_;
v___y_3751_ = v_a_3721_;
v___y_3752_ = v_a_3722_;
v___y_3753_ = v_a_3723_;
v___y_3754_ = v_a_3724_;
v___y_3755_ = v_a_3725_;
v___y_3756_ = v_a_3726_;
v___y_3757_ = v_a_3727_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_Meta_Grind_updateLastTag(v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec_ref(v___x_3855_);
v___x_3856_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3717_);
v___x_3857_ = l_Lean_indentExpr(v_e_3717_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3746_, v___x_3858_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_dec_ref(v___x_3859_);
v___y_3748_ = v_a_3718_;
v___y_3749_ = v_a_3719_;
v___y_3750_ = v_a_3720_;
v___y_3751_ = v_a_3721_;
v___y_3752_ = v_a_3722_;
v___y_3753_ = v_a_3723_;
v___y_3754_ = v_a_3724_;
v___y_3755_ = v_a_3725_;
v___y_3756_ = v_a_3726_;
v___y_3757_ = v_a_3727_;
goto v___jp_3747_;
}
else
{
lean_dec_ref(v_e_3717_);
return v___x_3859_;
}
}
else
{
lean_dec_ref(v_e_3717_);
return v___x_3855_;
}
}
}
v___jp_3729_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_box(0);
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
v___jp_3732_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_inc_ref(v_e_3717_);
v___x_3741_ = l_Lean_Meta_mkEqTrueCore(v_e_3717_, v___y_3733_);
v___x_3742_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3717_, v___x_3741_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
return v___x_3742_;
}
v___jp_3747_:
{
lean_object* v___x_3758_; 
lean_inc_ref(v_e_3717_);
v___x_3758_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3717_, v___y_3748_, v___y_3752_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; uint8_t v___x_3760_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = lean_unbox(v_a_3759_);
lean_dec(v_a_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; 
lean_inc_ref(v_e_3717_);
v___x_3761_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3717_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3816_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3816_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3816_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
uint8_t v___x_3766_; 
v___x_3766_ = lean_unbox(v_a_3762_);
lean_dec(v_a_3762_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
lean_dec_ref(v_e_3717_);
v___x_3767_ = lean_box(0);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3767_);
v___x_3769_ = v___x_3764_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
else
{
lean_object* v___x_3771_; 
lean_del_object(v___x_3764_);
lean_inc_ref(v_e_3717_);
v___x_3771_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3717_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref(v___x_3771_);
if (lean_obj_tag(v_a_3772_) == 1)
{
lean_object* v_options_3773_; uint8_t v_hasTrace_3774_; 
v_options_3773_ = lean_ctor_get(v___y_3756_, 2);
v_hasTrace_3774_ = lean_ctor_get_uint8(v_options_3773_, sizeof(void*)*1);
if (v_hasTrace_3774_ == 0)
{
lean_object* v_val_3775_; 
v_val_3775_ = lean_ctor_get(v_a_3772_, 0);
lean_inc(v_val_3775_);
lean_dec_ref(v_a_3772_);
v___y_3733_ = v_val_3775_;
v___y_3734_ = v___y_3748_;
v___y_3735_ = v___y_3750_;
v___y_3736_ = v___y_3752_;
v___y_3737_ = v___y_3754_;
v___y_3738_ = v___y_3755_;
v___y_3739_ = v___y_3756_;
v___y_3740_ = v___y_3757_;
goto v___jp_3732_;
}
else
{
lean_object* v_val_3776_; lean_object* v_inheritedTraceOptions_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v_val_3776_ = lean_ctor_get(v_a_3772_, 0);
lean_inc(v_val_3776_);
lean_dec_ref(v_a_3772_);
v_inheritedTraceOptions_3777_ = lean_ctor_get(v___y_3756_, 13);
v___x_3778_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___closed__6);
v___x_3779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3777_, v_options_3773_, v___x_3778_);
if (v___x_3779_ == 0)
{
v___y_3733_ = v_val_3776_;
v___y_3734_ = v___y_3748_;
v___y_3735_ = v___y_3750_;
v___y_3736_ = v___y_3752_;
v___y_3737_ = v___y_3754_;
v___y_3738_ = v___y_3755_;
v___y_3739_ = v___y_3756_;
v___y_3740_ = v___y_3757_;
goto v___jp_3732_;
}
else
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Meta_Grind_updateLastTag(v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v___x_3781_; 
lean_dec_ref(v___x_3780_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3755_);
lean_inc_ref(v___y_3754_);
lean_inc(v_val_3776_);
v___x_3781_ = lean_infer_type(v_val_3776_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = l_Lean_MessageData_ofExpr(v_a_3782_);
v___x_3784_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3746_, v___x_3783_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_dec_ref(v___x_3784_);
v___y_3733_ = v_val_3776_;
v___y_3734_ = v___y_3748_;
v___y_3735_ = v___y_3750_;
v___y_3736_ = v___y_3752_;
v___y_3737_ = v___y_3754_;
v___y_3738_ = v___y_3755_;
v___y_3739_ = v___y_3756_;
v___y_3740_ = v___y_3757_;
goto v___jp_3732_;
}
else
{
lean_dec(v_val_3776_);
lean_dec_ref(v_e_3717_);
return v___x_3784_;
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec(v_val_3776_);
lean_dec_ref(v_e_3717_);
v_a_3785_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3781_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3781_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_dec(v_val_3776_);
lean_dec_ref(v_e_3717_);
return v___x_3780_;
}
}
}
}
else
{
lean_object* v___x_3793_; 
lean_dec(v_a_3772_);
v___x_3793_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3752_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; uint8_t v___x_3795_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = lean_unbox(v_a_3794_);
lean_dec(v_a_3794_);
if (v___x_3795_ == 0)
{
lean_dec_ref(v_e_3717_);
goto v___jp_3729_;
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3796_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3797_ = l_Lean_indentExpr(v_e_3717_);
v___x_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = l_Lean_Meta_Sym_reportIssue(v___x_3798_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref(v___x_3799_);
goto v___jp_3729_;
}
else
{
return v___x_3799_;
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v_e_3717_);
v_a_3800_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3793_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3793_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v_e_3717_);
v_a_3808_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3771_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3771_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v_e_3717_);
v_a_3817_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3761_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3761_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
lean_object* v___x_3825_; 
lean_inc_ref(v_e_3717_);
v___x_3825_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3717_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3836_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_unbox(v_a_3826_);
lean_dec(v_a_3826_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
lean_del_object(v___x_3828_);
v___x_3831_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3717_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec_ref(v_e_3717_);
v___x_3832_ = lean_box(0);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3832_);
v___x_3834_ = v___x_3828_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_e_3717_);
v_a_3837_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3825_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3825_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec_ref(v_e_3717_);
v_a_3845_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3758_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3758_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec(v_a_3861_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3875_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3876_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3874_, v___x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3891_; 
lean_inc_ref(v_e_3879_);
v___x_3891_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3879_, v_a_3880_, v_a_3884_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3921_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3921_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3921_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_unbox(v_a_3892_);
lean_dec(v_a_3892_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; lean_object* v___x_3899_; 
lean_dec_ref(v_e_3879_);
v___x_3897_ = lean_box(0);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3897_);
v___x_3899_ = v___x_3894_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3897_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
else
{
lean_object* v___x_3901_; 
lean_del_object(v___x_3894_);
lean_inc_ref(v_e_3879_);
v___x_3901_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3912_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3912_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3912_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
uint8_t v___x_3906_; 
v___x_3906_ = lean_unbox(v_a_3902_);
lean_dec(v_a_3902_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; 
lean_del_object(v___x_3904_);
v___x_3907_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
return v___x_3907_;
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_dec_ref(v_e_3879_);
v___x_3908_ = lean_box(0);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3908_);
v___x_3910_ = v___x_3904_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec_ref(v_e_3879_);
v_a_3913_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3901_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3901_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec_ref(v_e_3879_);
v_a_3922_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3891_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3891_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec(v_a_3931_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3945_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3946_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3944_, v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
return v_res_3948_;
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
