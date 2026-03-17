// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Intro
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.Basic
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imp"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(254, 180, 127, 119, 35, 232, 80, 131)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Target not an implication or let-binding "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "entails_cons_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 192, 217, 126, 138, 217, 120, 234)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Ambient state list not a cons "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mintro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 222, 62, 246, 205, 225, 8, 203)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mintroPat_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 197, 23, 48, 210, 183, 157, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 196, 52, 121, 17, 165, 127, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mcases"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(121, 124, 66, 100, 237, 121, 142, 93)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 53, 195, 0, 35, 253, 177, 163)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "mintroPat∀_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 201, 27, 44, 199, 236, 234, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMIntro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 115, 63, 215, 129, 231, 252, 53)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__0(lean_object* v_val_1_, lean_object* v_inst_2_, lean_object* v_prf_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_mk_empty_array_with_capacity(v___x_4_);
v___x_6_ = lean_array_push(v___x_5_, v_val_1_);
v___x_7_ = 1;
v___x_8_ = 1;
v___x_9_ = lean_box(v___x_7_);
v___x_10_ = lean_box(v___x_7_);
v___x_11_ = lean_box(v___x_8_);
v___x_12_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_12_, 0, v___x_6_);
lean_closure_set(v___x_12_, 1, v_prf_3_);
lean_closure_set(v___x_12_, 2, v___x_9_);
lean_closure_set(v___x_12_, 3, v___x_10_);
lean_closure_set(v___x_12_, 4, v___x_11_);
v___x_13_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1(lean_object* v_inst_14_, lean_object* v_body_15_, lean_object* v_u_16_, lean_object* v_00_u03c3s_17_, lean_object* v_hyps_18_, lean_object* v_k_19_, lean_object* v_toBind_20_, lean_object* v_val_21_){
_start:
{
lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_inc_ref(v_val_21_);
v___f_22_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_val_21_);
lean_closure_set(v___f_22_, 1, v_inst_14_);
v___x_23_ = lean_expr_instantiate1(v_body_15_, v_val_21_);
lean_dec_ref(v_val_21_);
v___x_24_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_24_, 0, v_u_16_);
lean_ctor_set(v___x_24_, 1, v_00_u03c3s_17_);
lean_ctor_set(v___x_24_, 2, v_hyps_18_);
lean_ctor_set(v___x_24_, 3, v___x_23_);
v___x_25_ = lean_apply_1(v_k_19_, v___x_24_);
v___x_26_ = lean_apply_4(v_toBind_20_, lean_box(0), lean_box(0), v___x_25_, v___f_22_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed(lean_object* v_inst_27_, lean_object* v_body_28_, lean_object* v_u_29_, lean_object* v_00_u03c3s_30_, lean_object* v_hyps_31_, lean_object* v_k_32_, lean_object* v_toBind_33_, lean_object* v_val_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1(v_inst_27_, v_body_28_, v_u_29_, v_00_u03c3s_30_, v_hyps_31_, v_k_32_, v_toBind_33_, v_val_34_);
lean_dec_ref(v_body_28_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_type_38_, lean_object* v_value_39_, lean_object* v___f_40_, uint8_t v___x_41_, lean_object* v_name_42_){
_start:
{
uint8_t v___x_43_; lean_object* v___x_44_; 
v___x_43_ = 0;
v___x_44_ = l_Lean_Meta_withLetDecl___redArg(v_inst_36_, v_inst_37_, v_name_42_, v_type_38_, v_value_39_, v___f_40_, v___x_41_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed(lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_type_47_, lean_object* v_value_48_, lean_object* v___f_49_, lean_object* v___x_50_, lean_object* v_name_51_){
_start:
{
uint8_t v___x_1355__boxed_52_; lean_object* v_res_53_; 
v___x_1355__boxed_52_ = lean_unbox(v___x_50_);
v_res_53_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(v_inst_45_, v_inst_46_, v_type_47_, v_value_48_, v___f_49_, v___x_1355__boxed_52_, v_name_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3(lean_object* v___f_54_, lean_object* v_name_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_apply_1(v___f_54_, v_name_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(lean_object* v_declName_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Core_mkFreshUserName(v_declName_57_, v___y_60_, v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed(lean_object* v_declName_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(v_declName_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(lean_object* v_ident_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_71_, v___y_74_, v___y_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed(lean_object* v_ident_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(v_ident_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5(lean_object* v___x_88_, lean_object* v___x_89_, lean_object* v___x_90_, lean_object* v_u_91_, lean_object* v___x_92_, lean_object* v_fst_93_, lean_object* v_hyps_94_, lean_object* v_H_95_, lean_object* v___x_96_, lean_object* v_snd_97_, lean_object* v_toPure_98_, lean_object* v_prf_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_prf_107_; lean_object* v___x_108_; 
v___x_100_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0));
v___x_101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1));
v___x_102_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2));
v___x_103_ = l_Lean_Name_mkStr6(v___x_88_, v___x_89_, v___x_90_, v___x_100_, v___x_101_, v___x_102_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v_u_91_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = l_Lean_mkConst(v___x_103_, v___x_105_);
v_prf_107_ = l_Lean_mkApp7(v___x_106_, v___x_92_, v_fst_93_, v_hyps_94_, v_H_95_, v___x_96_, v_snd_97_, v_prf_99_);
v___x_108_ = lean_apply_2(v_toPure_98_, lean_box(0), v_prf_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6(lean_object* v_hyp_109_, lean_object* v_u_110_, lean_object* v_00_u03c3s_111_, lean_object* v_hyps_112_, lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v___x_115_, lean_object* v___x_116_, lean_object* v___x_117_, lean_object* v_toPure_118_, lean_object* v_k_119_, lean_object* v_toBind_120_, lean_object* v_____r_121_){
_start:
{
lean_object* v_H_122_; lean_object* v___x_123_; lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_H_122_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_109_);
lean_inc_ref(v_H_122_);
lean_inc_ref(v_hyps_112_);
lean_inc_ref(v_00_u03c3s_111_);
lean_inc(v_u_110_);
v___x_123_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_110_, v_00_u03c3s_111_, v_hyps_112_, v_H_122_);
v_fst_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_fst_124_);
v_snd_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_snd_125_);
lean_dec_ref(v___x_123_);
lean_inc_ref(v___x_117_);
lean_inc(v_fst_124_);
lean_inc(v_u_110_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5), 12, 11);
lean_closure_set(v___f_126_, 0, v___x_113_);
lean_closure_set(v___f_126_, 1, v___x_114_);
lean_closure_set(v___f_126_, 2, v___x_115_);
lean_closure_set(v___f_126_, 3, v_u_110_);
lean_closure_set(v___f_126_, 4, v___x_116_);
lean_closure_set(v___f_126_, 5, v_fst_124_);
lean_closure_set(v___f_126_, 6, v_hyps_112_);
lean_closure_set(v___f_126_, 7, v_H_122_);
lean_closure_set(v___f_126_, 8, v___x_117_);
lean_closure_set(v___f_126_, 9, v_snd_125_);
lean_closure_set(v___f_126_, 10, v_toPure_118_);
v___x_127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_127_, 0, v_u_110_);
lean_ctor_set(v___x_127_, 1, v_00_u03c3s_111_);
lean_ctor_set(v___x_127_, 2, v_fst_124_);
lean_ctor_set(v___x_127_, 3, v___x_117_);
v___x_128_ = lean_apply_1(v_k_119_, v___x_127_);
v___x_129_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_128_, v___f_126_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(lean_object* v_fst_130_, lean_object* v___x_131_, lean_object* v_u_132_, lean_object* v_00_u03c3s_133_, lean_object* v_hyps_134_, lean_object* v___x_135_, lean_object* v___x_136_, lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v___x_139_, lean_object* v_toPure_140_, lean_object* v_k_141_, lean_object* v_toBind_142_, lean_object* v_snd_143_, uint8_t v___x_144_, lean_object* v_inst_145_, lean_object* v_uniq_146_){
_start:
{
lean_object* v_hyp_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_hyp_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_147_, 0, v_fst_130_);
lean_ctor_set(v_hyp_147_, 1, v_uniq_146_);
lean_ctor_set(v_hyp_147_, 2, v___x_131_);
lean_inc(v_toBind_142_);
lean_inc_ref(v___x_138_);
lean_inc_ref(v_hyp_147_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6), 13, 12);
lean_closure_set(v___f_148_, 0, v_hyp_147_);
lean_closure_set(v___f_148_, 1, v_u_132_);
lean_closure_set(v___f_148_, 2, v_00_u03c3s_133_);
lean_closure_set(v___f_148_, 3, v_hyps_134_);
lean_closure_set(v___f_148_, 4, v___x_135_);
lean_closure_set(v___f_148_, 5, v___x_136_);
lean_closure_set(v___f_148_, 6, v___x_137_);
lean_closure_set(v___f_148_, 7, v___x_138_);
lean_closure_set(v___f_148_, 8, v___x_139_);
lean_closure_set(v___f_148_, 9, v_toPure_140_);
lean_closure_set(v___f_148_, 10, v_k_141_);
lean_closure_set(v___f_148_, 11, v_toBind_142_);
v___x_149_ = lean_box(v___x_144_);
v___x_150_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed), 9, 4);
lean_closure_set(v___x_150_, 0, v_snd_143_);
lean_closure_set(v___x_150_, 1, v___x_138_);
lean_closure_set(v___x_150_, 2, v_hyp_147_);
lean_closure_set(v___x_150_, 3, v___x_149_);
v___x_151_ = lean_apply_2(v_inst_145_, lean_box(0), v___x_150_);
v___x_152_ = lean_apply_4(v_toBind_142_, lean_box(0), lean_box(0), v___x_151_, v___f_148_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_fst_153_ = _args[0];
lean_object* v___x_154_ = _args[1];
lean_object* v_u_155_ = _args[2];
lean_object* v_00_u03c3s_156_ = _args[3];
lean_object* v_hyps_157_ = _args[4];
lean_object* v___x_158_ = _args[5];
lean_object* v___x_159_ = _args[6];
lean_object* v___x_160_ = _args[7];
lean_object* v___x_161_ = _args[8];
lean_object* v___x_162_ = _args[9];
lean_object* v_toPure_163_ = _args[10];
lean_object* v_k_164_ = _args[11];
lean_object* v_toBind_165_ = _args[12];
lean_object* v_snd_166_ = _args[13];
lean_object* v___x_167_ = _args[14];
lean_object* v_inst_168_ = _args[15];
lean_object* v_uniq_169_ = _args[16];
_start:
{
uint8_t v___x_1486__boxed_170_; lean_object* v_res_171_; 
v___x_1486__boxed_170_ = lean_unbox(v___x_167_);
v_res_171_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(v_fst_153_, v___x_154_, v_u_155_, v_00_u03c3s_156_, v_hyps_157_, v___x_158_, v___x_159_, v___x_160_, v___x_161_, v___x_162_, v_toPure_163_, v_k_164_, v_toBind_165_, v_snd_166_, v___x_1486__boxed_170_, v_inst_168_, v_uniq_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(lean_object* v___x_172_, lean_object* v_u_173_, lean_object* v_00_u03c3s_174_, lean_object* v_hyps_175_, lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v___x_180_, lean_object* v_toPure_181_, lean_object* v_k_182_, lean_object* v_toBind_183_, uint8_t v___x_184_, lean_object* v_inst_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v_____x_188_){
_start:
{
lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_fst_189_ = lean_ctor_get(v_____x_188_, 0);
lean_inc(v_fst_189_);
v_snd_190_ = lean_ctor_get(v_____x_188_, 1);
lean_inc(v_snd_190_);
lean_dec_ref(v_____x_188_);
v___x_191_ = lean_box(v___x_184_);
lean_inc(v_inst_185_);
lean_inc(v_toBind_183_);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_192_, 0, v_fst_189_);
lean_closure_set(v___f_192_, 1, v___x_172_);
lean_closure_set(v___f_192_, 2, v_u_173_);
lean_closure_set(v___f_192_, 3, v_00_u03c3s_174_);
lean_closure_set(v___f_192_, 4, v_hyps_175_);
lean_closure_set(v___f_192_, 5, v___x_176_);
lean_closure_set(v___f_192_, 6, v___x_177_);
lean_closure_set(v___f_192_, 7, v___x_178_);
lean_closure_set(v___f_192_, 8, v___x_179_);
lean_closure_set(v___f_192_, 9, v___x_180_);
lean_closure_set(v___f_192_, 10, v_toPure_181_);
lean_closure_set(v___f_192_, 11, v_k_182_);
lean_closure_set(v___f_192_, 12, v_toBind_183_);
lean_closure_set(v___f_192_, 13, v_snd_190_);
lean_closure_set(v___f_192_, 14, v___x_191_);
lean_closure_set(v___f_192_, 15, v_inst_185_);
v___x_193_ = l_Lean_mkFreshId___redArg(v___x_186_, v___x_187_);
v___x_194_ = lean_apply_2(v_inst_185_, lean_box(0), v___x_193_);
v___x_195_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_194_, v___f_192_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed(lean_object** _args){
lean_object* v___x_196_ = _args[0];
lean_object* v_u_197_ = _args[1];
lean_object* v_00_u03c3s_198_ = _args[2];
lean_object* v_hyps_199_ = _args[3];
lean_object* v___x_200_ = _args[4];
lean_object* v___x_201_ = _args[5];
lean_object* v___x_202_ = _args[6];
lean_object* v___x_203_ = _args[7];
lean_object* v___x_204_ = _args[8];
lean_object* v_toPure_205_ = _args[9];
lean_object* v_k_206_ = _args[10];
lean_object* v_toBind_207_ = _args[11];
lean_object* v___x_208_ = _args[12];
lean_object* v_inst_209_ = _args[13];
lean_object* v___x_210_ = _args[14];
lean_object* v___x_211_ = _args[15];
lean_object* v_____x_212_ = _args[16];
_start:
{
uint8_t v___x_1524__boxed_213_; lean_object* v_res_214_; 
v___x_1524__boxed_213_ = lean_unbox(v___x_208_);
v_res_214_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(v___x_196_, v_u_197_, v_00_u03c3s_198_, v_hyps_199_, v___x_200_, v___x_201_, v___x_202_, v___x_203_, v___x_204_, v_toPure_205_, v_k_206_, v_toBind_207_, v___x_1524__boxed_213_, v_inst_209_, v___x_210_, v___x_211_, v_____x_212_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0);
v___x_217_ = l_ReaderT_instMonad___redArg(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_225_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5));
v___x_226_ = l_Lean_monadNameGeneratorLift___redArg(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9(void){
_start:
{
lean_object* v___x_227_; lean_object* v___f_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8);
v___f_228_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4));
v___x_229_ = l_Lean_monadNameGeneratorLift___redArg(v___f_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10(void){
_start:
{
lean_object* v___x_230_; lean_object* v___f_231_; 
v___x_230_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_231_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_231_, 0, v___x_230_);
return v___f_231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11(void){
_start:
{
lean_object* v___x_232_; lean_object* v___f_233_; 
v___x_232_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_233_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_233_, 0, v___x_232_);
return v___f_233_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12(void){
_start:
{
lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; 
v___f_234_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11);
v___f_235_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___f_235_);
lean_ctor_set(v___x_236_, 1, v___f_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13(void){
_start:
{
lean_object* v___x_237_; lean_object* v___f_238_; 
v___x_237_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12);
v___f_238_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_238_, 0, v___x_237_);
return v___f_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14(void){
_start:
{
lean_object* v___x_239_; lean_object* v___f_240_; 
v___x_239_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12);
v___f_240_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_240_, 0, v___x_239_);
return v___f_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15(void){
_start:
{
lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___x_243_; 
v___f_241_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14);
v___f_242_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___f_242_);
lean_ctor_set(v___x_243_, 1, v___f_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; 
v___x_245_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5));
v___f_247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16));
v___x_248_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_247_, v___x_246_, v___x_245_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18(void){
_start:
{
lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___x_252_; 
v___x_249_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17);
v___f_250_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4));
v___f_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16));
v___x_252_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_251_, v___f_250_, v___x_249_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_goal_276_, lean_object* v_ident_277_, lean_object* v_k_278_){
_start:
{
lean_object* v___x_279_; lean_object* v_toApplicative_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_405_; 
v___x_279_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_279_, 1);
lean_dec(v_unused_406_);
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_405_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_toApplicative_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_405_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_toFunctor_284_; lean_object* v_toSeq_285_; lean_object* v_toSeqLeft_286_; lean_object* v_toSeqRight_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_403_; 
v_toFunctor_284_ = lean_ctor_get(v_toApplicative_280_, 0);
v_toSeq_285_ = lean_ctor_get(v_toApplicative_280_, 2);
v_toSeqLeft_286_ = lean_ctor_get(v_toApplicative_280_, 3);
v_toSeqRight_287_ = lean_ctor_get(v_toApplicative_280_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v_toApplicative_280_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_toApplicative_280_, 1);
lean_dec(v_unused_404_);
v___x_289_ = v_toApplicative_280_;
v_isShared_290_ = v_isSharedCheck_403_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_toSeqRight_287_);
lean_inc(v_toSeqLeft_286_);
lean_inc(v_toSeq_285_);
lean_inc(v_toFunctor_284_);
lean_dec(v_toApplicative_280_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_403_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___f_293_; lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___x_300_; 
v___f_291_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_292_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref(v_toFunctor_284_);
v___f_293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_293_, 0, v_toFunctor_284_);
v___f_294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_294_, 0, v_toFunctor_284_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___f_293_);
lean_ctor_set(v___x_295_, 1, v___f_294_);
v___f_296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_296_, 0, v_toSeqRight_287_);
v___f_297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_297_, 0, v_toSeqLeft_286_);
v___f_298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_298_, 0, v_toSeq_285_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 4, v___f_296_);
lean_ctor_set(v___x_289_, 3, v___f_297_);
lean_ctor_set(v___x_289_, 2, v___f_298_);
lean_ctor_set(v___x_289_, 1, v___f_291_);
lean_ctor_set(v___x_289_, 0, v___x_295_);
v___x_300_ = v___x_289_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___f_291_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v___f_298_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v___f_297_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___f_296_);
v___x_300_ = v_reuseFailAlloc_402_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___f_292_);
lean_ctor_set(v___x_282_, 0, v___x_300_);
v___x_302_ = v___x_282_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___f_292_);
v___x_302_ = v_reuseFailAlloc_401_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v_toApplicative_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_399_; 
v___x_303_ = l_ReaderT_instMonad___redArg(v___x_302_);
v_toApplicative_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_303_, 1);
lean_dec(v_unused_400_);
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_399_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_toApplicative_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_399_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_toFunctor_308_; lean_object* v_toSeq_309_; lean_object* v_toSeqLeft_310_; lean_object* v_toSeqRight_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_397_; 
v_toFunctor_308_ = lean_ctor_get(v_toApplicative_304_, 0);
v_toSeq_309_ = lean_ctor_get(v_toApplicative_304_, 2);
v_toSeqLeft_310_ = lean_ctor_get(v_toApplicative_304_, 3);
v_toSeqRight_311_ = lean_ctor_get(v_toApplicative_304_, 4);
v_isSharedCheck_397_ = !lean_is_exclusive(v_toApplicative_304_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_toApplicative_304_, 1);
lean_dec(v_unused_398_);
v___x_313_ = v_toApplicative_304_;
v_isShared_314_ = v_isSharedCheck_397_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_toSeqRight_311_);
lean_inc(v_toSeqLeft_310_);
lean_inc(v_toSeq_309_);
lean_inc(v_toFunctor_308_);
lean_dec(v_toApplicative_304_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_397_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___x_324_; 
v___f_315_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_308_);
v___f_317_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_317_, 0, v_toFunctor_308_);
v___f_318_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_318_, 0, v_toFunctor_308_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___f_317_);
lean_ctor_set(v___x_319_, 1, v___f_318_);
v___f_320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_320_, 0, v_toSeqRight_311_);
v___f_321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_321_, 0, v_toSeqLeft_310_);
v___f_322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_322_, 0, v_toSeq_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___f_320_);
lean_ctor_set(v___x_313_, 3, v___f_321_);
lean_ctor_set(v___x_313_, 2, v___f_322_);
lean_ctor_set(v___x_313_, 1, v___f_315_);
lean_ctor_set(v___x_313_, 0, v___x_319_);
v___x_324_ = v___x_313_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___f_315_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v___f_322_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v___f_321_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___f_320_);
v___x_324_ = v_reuseFailAlloc_396_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___f_316_);
lean_ctor_set(v___x_306_, 0, v___x_324_);
v___x_326_ = v___x_306_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___f_316_);
v___x_326_ = v_reuseFailAlloc_395_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_toMonadRef_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_toApplicative_334_; lean_object* v_toBind_335_; lean_object* v_toPure_336_; lean_object* v_u_337_; lean_object* v_00_u03c3s_338_; lean_object* v_hyps_339_; lean_object* v_target_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_327_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9);
v___x_328_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_329_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18);
v_toMonadRef_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_toMonadRef_330_);
v___x_331_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_326_);
v___x_332_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_331_, v___x_326_);
v___x_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_328_);
lean_ctor_set(v___x_333_, 1, v_toMonadRef_330_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
v_toApplicative_334_ = lean_ctor_get(v_inst_273_, 0);
v_toBind_335_ = lean_ctor_get(v_inst_273_, 1);
v_toPure_336_ = lean_ctor_get(v_toApplicative_334_, 1);
v_u_337_ = lean_ctor_get(v_goal_276_, 0);
lean_inc(v_u_337_);
v_00_u03c3s_338_ = lean_ctor_get(v_goal_276_, 1);
lean_inc_ref(v_00_u03c3s_338_);
v_hyps_339_ = lean_ctor_get(v_goal_276_, 2);
lean_inc_ref(v_hyps_339_);
v_target_340_ = lean_ctor_get(v_goal_276_, 3);
lean_inc_ref(v_target_340_);
lean_dec_ref(v_goal_276_);
v___x_341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19));
v___x_342_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20));
v___x_343_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21));
v___x_344_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23));
v___x_345_ = lean_unsigned_to_nat(3u);
v___x_346_ = l_Lean_Expr_isAppOfArity(v_target_340_, v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
if (lean_obj_tag(v_target_340_) == 8)
{
lean_object* v_declName_347_; lean_object* v_type_348_; lean_object* v_value_349_; lean_object* v_body_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
lean_inc(v_toPure_336_);
lean_inc(v_toBind_335_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_326_);
v_declName_347_ = lean_ctor_get(v_target_340_, 0);
lean_inc(v_declName_347_);
v_type_348_ = lean_ctor_get(v_target_340_, 1);
lean_inc_ref(v_type_348_);
v_value_349_ = lean_ctor_get(v_target_340_, 2);
lean_inc_ref(v_value_349_);
v_body_350_ = lean_ctor_get(v_target_340_, 3);
lean_inc_ref(v_body_350_);
lean_dec_ref(v_target_340_);
lean_inc(v_toBind_335_);
lean_inc(v_inst_275_);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_351_, 0, v_inst_275_);
lean_closure_set(v___f_351_, 1, v_body_350_);
lean_closure_set(v___f_351_, 2, v_u_337_);
lean_closure_set(v___f_351_, 3, v_00_u03c3s_338_);
lean_closure_set(v___f_351_, 4, v_hyps_339_);
lean_closure_set(v___f_351_, 5, v_k_278_);
lean_closure_set(v___f_351_, 6, v_toBind_335_);
v___x_352_ = lean_box(v___x_346_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_353_, 0, v_inst_274_);
lean_closure_set(v___f_353_, 1, v_inst_273_);
lean_closure_set(v___f_353_, 2, v_type_348_);
lean_closure_set(v___f_353_, 3, v_value_349_);
lean_closure_set(v___f_353_, 4, v___f_351_);
lean_closure_set(v___f_353_, 5, v___x_352_);
v___x_354_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
lean_inc(v_ident_277_);
v___x_355_ = l_Lean_Syntax_isOfKind(v_ident_277_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_toPure_336_);
lean_dec(v_ident_277_);
v___f_356_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_356_, 0, v___f_353_);
v___f_357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_357_, 0, v_declName_347_);
v___x_358_ = lean_apply_2(v_inst_275_, lean_box(0), v___f_357_);
v___x_359_ = lean_apply_4(v_toBind_335_, lean_box(0), lean_box(0), v___x_358_, v___f_356_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v_name_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v_name_361_ = l_Lean_Syntax_getArg(v_ident_277_, v___x_360_);
lean_dec(v_ident_277_);
v___x_362_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28));
lean_inc(v_name_361_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_name_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_name_361_);
lean_dec(v_toPure_336_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_364_, 0, v___f_353_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_365_, 0, v_declName_347_);
v___x_366_ = lean_apply_2(v_inst_275_, lean_box(0), v___f_365_);
v___x_367_ = lean_apply_4(v_toBind_335_, lean_box(0), lean_box(0), v___x_366_, v___f_364_);
return v___x_367_;
}
else
{
lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v_declName_347_);
lean_dec(v_inst_275_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_368_, 0, v___f_353_);
v___x_369_ = l_Lean_TSyntax_getId(v_name_361_);
lean_dec(v_name_361_);
v___x_370_ = lean_apply_2(v_toPure_336_, lean_box(0), v___x_369_);
v___x_371_ = lean_apply_4(v_toBind_335_, lean_box(0), lean_box(0), v___x_370_, v___f_368_);
return v___x_371_;
}
}
}
else
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_hyps_339_);
lean_dec_ref(v_00_u03c3s_338_);
lean_dec(v_u_337_);
lean_dec(v_k_278_);
lean_dec(v_ident_277_);
lean_dec_ref(v_inst_274_);
v_isSharedCheck_382_ = !lean_is_exclusive(v_inst_273_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; lean_object* v_unused_384_; 
v_unused_383_ = lean_ctor_get(v_inst_273_, 1);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_inst_273_, 0);
lean_dec(v_unused_384_);
v___x_373_ = v_inst_273_;
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
else
{
lean_dec(v_inst_273_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30);
v___x_376_ = l_Lean_MessageData_ofExpr(v_target_340_);
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 7);
lean_ctor_set(v___x_373_, 1, v___x_376_);
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_381_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = l_Lean_throwError___redArg(v___x_326_, v___x_333_, v___x_378_);
v___x_380_ = lean_apply_2(v_inst_275_, lean_box(0), v___x_379_);
return v___x_380_;
}
}
}
}
else
{
lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_inc(v_toPure_336_);
lean_inc(v_toBind_335_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v_inst_274_);
lean_dec_ref(v_inst_273_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed), 6, 1);
lean_closure_set(v___f_385_, 0, v_ident_277_);
v___x_386_ = l_Lean_Expr_appFn_x21(v_target_340_);
v___x_387_ = l_Lean_Expr_appFn_x21(v___x_386_);
v___x_388_ = l_Lean_Expr_appArg_x21(v___x_387_);
lean_dec_ref(v___x_387_);
v___x_389_ = l_Lean_Expr_appArg_x21(v___x_386_);
lean_dec_ref(v___x_386_);
v___x_390_ = l_Lean_Expr_appArg_x21(v_target_340_);
lean_dec_ref(v_target_340_);
v___x_391_ = lean_box(v___x_346_);
lean_inc(v_inst_275_);
lean_inc(v_toBind_335_);
v___f_392_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_392_, 0, v___x_389_);
lean_closure_set(v___f_392_, 1, v_u_337_);
lean_closure_set(v___f_392_, 2, v_00_u03c3s_338_);
lean_closure_set(v___f_392_, 3, v_hyps_339_);
lean_closure_set(v___f_392_, 4, v___x_341_);
lean_closure_set(v___f_392_, 5, v___x_342_);
lean_closure_set(v___f_392_, 6, v___x_343_);
lean_closure_set(v___f_392_, 7, v___x_388_);
lean_closure_set(v___f_392_, 8, v___x_390_);
lean_closure_set(v___f_392_, 9, v_toPure_336_);
lean_closure_set(v___f_392_, 10, v_k_278_);
lean_closure_set(v___f_392_, 11, v_toBind_335_);
lean_closure_set(v___f_392_, 12, v___x_391_);
lean_closure_set(v___f_392_, 13, v_inst_275_);
lean_closure_set(v___f_392_, 14, v___x_326_);
lean_closure_set(v___f_392_, 15, v___x_327_);
v___x_393_ = lean_apply_2(v_inst_275_, lean_box(0), v___f_385_);
v___x_394_ = lean_apply_4(v_toBind_335_, lean_box(0), lean_box(0), v___x_393_, v___f_392_);
return v___x_394_;
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro(lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_goal_411_, lean_object* v_ident_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_goal_411_, v_ident_412_, v_k_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0(lean_object* v_u_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v_hyps_424_, lean_object* v_target_425_, lean_object* v_toPure_426_, lean_object* v_prf_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_428_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v_u_421_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_mkConst(v___x_428_, v___x_430_);
v___x_432_ = l_Lean_mkApp5(v___x_431_, v___x_422_, v___x_423_, v_hyps_424_, v_target_425_, v_prf_427_);
v___x_433_ = lean_apply_2(v_toPure_426_, lean_box(0), v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(lean_object* v___x_434_, uint8_t v___x_435_, uint8_t v___x_436_, lean_object* v_inst_437_, lean_object* v_toBind_438_, lean_object* v___f_439_, lean_object* v_prf_440_){
_start:
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_441_ = 1;
v___x_442_ = lean_box(v___x_435_);
v___x_443_ = lean_box(v___x_436_);
v___x_444_ = lean_box(v___x_435_);
v___x_445_ = lean_box(v___x_436_);
v___x_446_ = lean_box(v___x_441_);
v___x_447_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_447_, 0, v___x_434_);
lean_closure_set(v___x_447_, 1, v_prf_440_);
lean_closure_set(v___x_447_, 2, v___x_442_);
lean_closure_set(v___x_447_, 3, v___x_443_);
lean_closure_set(v___x_447_, 4, v___x_444_);
lean_closure_set(v___x_447_, 5, v___x_445_);
lean_closure_set(v___x_447_, 6, v___x_446_);
v___x_448_ = lean_apply_2(v_inst_437_, lean_box(0), v___x_447_);
v___x_449_ = lean_apply_4(v_toBind_438_, lean_box(0), lean_box(0), v___x_448_, v___f_439_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed(lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v_inst_453_, lean_object* v_toBind_454_, lean_object* v___f_455_, lean_object* v_prf_456_){
_start:
{
uint8_t v___x_2296__boxed_457_; uint8_t v___x_2297__boxed_458_; lean_object* v_res_459_; 
v___x_2296__boxed_457_ = lean_unbox(v___x_451_);
v___x_2297__boxed_458_ = lean_unbox(v___x_452_);
v_res_459_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(v___x_450_, v___x_2296__boxed_457_, v___x_2297__boxed_458_, v_inst_453_, v_toBind_454_, v___f_455_, v_prf_456_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(lean_object* v___x_460_, lean_object* v_ident_461_, uint8_t v___x_462_, lean_object* v_hyps_463_, lean_object* v___x_464_, lean_object* v_inst_465_, lean_object* v_toBind_466_, lean_object* v___f_467_, lean_object* v_target_468_, lean_object* v_u_469_, lean_object* v_k_470_, lean_object* v_map_471_, lean_object* v_s_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_lctx_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_lctx_478_ = lean_ctor_get(v___y_473_, 2);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_460_);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc_ref(v_s_472_);
lean_inc_ref(v_lctx_478_);
v___x_480_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_461_, v_lctx_478_, v_s_472_, v___x_479_, v___x_462_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref(v___x_480_);
lean_inc_ref(v_s_472_);
v___x_481_ = l_Lean_Expr_app___override(v_hyps_463_, v_s_472_);
lean_inc_ref(v___x_464_);
v___x_482_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_464_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_485_ = lean_array_push(v___x_484_, v_s_472_);
v___x_486_ = 0;
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_box(v___x_462_);
lean_inc(v_toBind_466_);
lean_inc_ref(v___x_485_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_489_, 0, v___x_485_);
lean_closure_set(v___f_489_, 1, v___x_487_);
lean_closure_set(v___f_489_, 2, v___x_488_);
lean_closure_set(v___f_489_, 3, v_inst_465_);
lean_closure_set(v___f_489_, 4, v_toBind_466_);
lean_closure_set(v___f_489_, 5, v___f_467_);
v___x_490_ = l_Lean_Expr_betaRev(v_target_468_, v___x_485_, v___x_486_, v___x_486_);
lean_dec_ref(v___x_485_);
v___x_491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_491_, 0, v_u_469_);
lean_ctor_set(v___x_491_, 1, v___x_464_);
lean_ctor_set(v___x_491_, 2, v___x_482_);
lean_ctor_set(v___x_491_, 3, v___x_490_);
v___x_492_ = lean_apply_1(v_k_470_, v___x_491_);
v___x_493_ = lean_apply_4(v_toBind_466_, lean_box(0), lean_box(0), v___x_492_, v___f_489_);
v___x_494_ = lean_apply_7(v_map_471_, lean_box(0), v___x_493_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, lean_box(0));
return v___x_494_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec_ref(v_s_472_);
lean_dec_ref(v_map_471_);
lean_dec(v_k_470_);
lean_dec(v_u_469_);
lean_dec_ref(v_target_468_);
lean_dec(v___f_467_);
lean_dec(v_toBind_466_);
lean_dec(v_inst_465_);
lean_dec_ref(v___x_464_);
lean_dec_ref(v_hyps_463_);
v_a_495_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_480_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_480_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_503_ = _args[0];
lean_object* v_ident_504_ = _args[1];
lean_object* v___x_505_ = _args[2];
lean_object* v_hyps_506_ = _args[3];
lean_object* v___x_507_ = _args[4];
lean_object* v_inst_508_ = _args[5];
lean_object* v_toBind_509_ = _args[6];
lean_object* v___f_510_ = _args[7];
lean_object* v_target_511_ = _args[8];
lean_object* v_u_512_ = _args[9];
lean_object* v_k_513_ = _args[10];
lean_object* v_map_514_ = _args[11];
lean_object* v_s_515_ = _args[12];
lean_object* v___y_516_ = _args[13];
lean_object* v___y_517_ = _args[14];
lean_object* v___y_518_ = _args[15];
lean_object* v___y_519_ = _args[16];
lean_object* v___y_520_ = _args[17];
_start:
{
uint8_t v___x_2329__boxed_521_; lean_object* v_res_522_; 
v___x_2329__boxed_521_ = lean_unbox(v___x_505_);
v_res_522_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(v___x_503_, v_ident_504_, v___x_2329__boxed_521_, v_hyps_506_, v___x_507_, v_inst_508_, v_toBind_509_, v___f_510_, v_target_511_, v_u_512_, v_k_513_, v_map_514_, v_s_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v_res_522_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(lean_object* v_goal_534_, lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v_toPure_537_, lean_object* v_ident_538_, lean_object* v_inst_539_, lean_object* v_toBind_540_, lean_object* v_k_541_, lean_object* v___x_542_, lean_object* v_map_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_u_549_; lean_object* v_00_u03c3s_550_; lean_object* v_hyps_551_; lean_object* v_target_552_; lean_object* v___x_553_; 
v_u_549_ = lean_ctor_get(v_goal_534_, 0);
lean_inc(v_u_549_);
v_00_u03c3s_550_ = lean_ctor_get(v_goal_534_, 1);
lean_inc_ref(v_00_u03c3s_550_);
v_hyps_551_ = lean_ctor_get(v_goal_534_, 2);
lean_inc_ref(v_hyps_551_);
v_target_552_ = lean_ctor_get(v_goal_534_, 3);
lean_inc_ref(v_target_552_);
lean_dec_ref(v_goal_534_);
lean_inc(v___y_547_);
lean_inc_ref(v___y_546_);
lean_inc(v___y_545_);
lean_inc_ref(v___y_544_);
lean_inc_ref(v_00_u03c3s_550_);
v___x_553_ = lean_whnf(v_00_u03c3s_550_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_556_ = lean_unsigned_to_nat(3u);
v___x_557_ = l_Lean_Expr_isAppOfArity(v_a_554_, v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_2220__overap_561_; lean_object* v___x_562_; 
lean_dec(v_a_554_);
lean_dec_ref(v_target_552_);
lean_dec_ref(v_hyps_551_);
lean_dec(v_u_549_);
lean_dec_ref(v_map_543_);
lean_dec_ref(v___x_542_);
lean_dec(v_k_541_);
lean_dec(v_toBind_540_);
lean_dec(v_inst_539_);
lean_dec(v_ident_538_);
lean_dec(v_toPure_537_);
v___x_558_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_559_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_550_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_2220__overap_561_ = l_Lean_throwError___redArg(v___x_535_, v___x_536_, v___x_560_);
v___x_562_ = lean_apply_5(v___x_2220__overap_561_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, lean_box(0));
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
lean_dec_ref(v_00_u03c3s_550_);
lean_dec_ref(v___x_536_);
v___x_563_ = l_Lean_Expr_appFn_x21(v_a_554_);
v___x_564_ = l_Lean_Expr_appArg_x21(v___x_563_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_Lean_Expr_appArg_x21(v_a_554_);
lean_dec(v_a_554_);
lean_inc_ref(v_target_552_);
lean_inc_ref(v_hyps_551_);
lean_inc_ref(v___x_564_);
lean_inc_ref(v___x_565_);
lean_inc(v_u_549_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0), 7, 6);
lean_closure_set(v___f_566_, 0, v_u_549_);
lean_closure_set(v___f_566_, 1, v___x_565_);
lean_closure_set(v___f_566_, 2, v___x_564_);
lean_closure_set(v___f_566_, 3, v_hyps_551_);
lean_closure_set(v___f_566_, 4, v_target_552_);
lean_closure_set(v___f_566_, 5, v_toPure_537_);
v___x_567_ = lean_box(v___x_557_);
lean_inc(v_ident_538_);
lean_inc_ref(v___x_564_);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed), 18, 12);
lean_closure_set(v___f_568_, 0, v___x_564_);
lean_closure_set(v___f_568_, 1, v_ident_538_);
lean_closure_set(v___f_568_, 2, v___x_567_);
lean_closure_set(v___f_568_, 3, v_hyps_551_);
lean_closure_set(v___f_568_, 4, v___x_565_);
lean_closure_set(v___f_568_, 5, v_inst_539_);
lean_closure_set(v___f_568_, 6, v_toBind_540_);
lean_closure_set(v___f_568_, 7, v___f_566_);
lean_closure_set(v___f_568_, 8, v_target_552_);
lean_closure_set(v___f_568_, 9, v_u_549_);
lean_closure_set(v___f_568_, 10, v_k_541_);
lean_closure_set(v___f_568_, 11, v_map_543_);
v___x_569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
lean_inc(v_ident_538_);
v___x_570_ = l_Lean_Syntax_isOfKind(v_ident_538_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_ident_538_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
lean_inc(v___y_547_);
lean_inc_ref(v___y_546_);
v___x_572_ = l_Lean_Core_mkFreshUserName(v___x_571_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_2235__overap_574_; lean_object* v___x_575_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
v___x_2235__overap_574_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_542_, v___x_535_, v_a_573_, v___x_564_, v___f_568_);
v___x_575_ = lean_apply_5(v___x_2235__overap_574_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, lean_box(0));
return v___x_575_;
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v___f_568_);
lean_dec_ref(v___x_564_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v___x_535_);
v_a_576_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_572_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_572_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = l_Lean_Syntax_getArg(v_ident_538_, v___x_584_);
lean_dec(v_ident_538_);
v___x_586_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28));
lean_inc(v___x_585_);
v___x_587_ = l_Lean_Syntax_isOfKind(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v___x_585_);
v___x_588_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
lean_inc(v___y_547_);
lean_inc_ref(v___y_546_);
v___x_589_ = l_Lean_Core_mkFreshUserName(v___x_588_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_2249__overap_591_; lean_object* v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
v___x_2249__overap_591_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_542_, v___x_535_, v_a_590_, v___x_564_, v___f_568_);
v___x_592_ = lean_apply_5(v___x_2249__overap_591_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, lean_box(0));
return v___x_592_;
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v___f_568_);
lean_dec_ref(v___x_564_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v___x_535_);
v_a_593_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_589_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_2254__overap_602_; lean_object* v___x_603_; 
v___x_601_ = l_Lean_TSyntax_getId(v___x_585_);
lean_dec(v___x_585_);
v___x_2254__overap_602_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_542_, v___x_535_, v___x_601_, v___x_564_, v___f_568_);
v___x_603_ = lean_apply_5(v___x_2254__overap_602_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, lean_box(0));
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_target_552_);
lean_dec_ref(v_hyps_551_);
lean_dec_ref(v_00_u03c3s_550_);
lean_dec(v_u_549_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_map_543_);
lean_dec_ref(v___x_542_);
lean_dec(v_k_541_);
lean_dec(v_toBind_540_);
lean_dec(v_inst_539_);
lean_dec(v_ident_538_);
lean_dec(v_toPure_537_);
lean_dec_ref(v___x_536_);
lean_dec_ref(v___x_535_);
v_a_604_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_553_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_553_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed(lean_object* v_goal_612_, lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_toPure_615_, lean_object* v_ident_616_, lean_object* v_inst_617_, lean_object* v_toBind_618_, lean_object* v_k_619_, lean_object* v___x_620_, lean_object* v_map_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(v_goal_612_, v___x_613_, v___x_614_, v_toPure_615_, v_ident_616_, v_inst_617_, v_toBind_618_, v_k_619_, v___x_620_, v_map_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_goal_631_, lean_object* v_ident_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; lean_object* v_toApplicative_635_; lean_object* v_toFunctor_636_; lean_object* v_toSeq_637_; lean_object* v_toSeqLeft_638_; lean_object* v_toSeqRight_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_730_; 
v___x_634_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_toApplicative_635_);
v_toFunctor_636_ = lean_ctor_get(v_toApplicative_635_, 0);
v_toSeq_637_ = lean_ctor_get(v_toApplicative_635_, 2);
v_toSeqLeft_638_ = lean_ctor_get(v_toApplicative_635_, 3);
v_toSeqRight_639_ = lean_ctor_get(v_toApplicative_635_, 4);
v_isSharedCheck_730_ = !lean_is_exclusive(v_toApplicative_635_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_toApplicative_635_, 1);
lean_dec(v_unused_731_);
v___x_641_ = v_toApplicative_635_;
v_isShared_642_ = v_isSharedCheck_730_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_toSeqRight_639_);
lean_inc(v_toSeqLeft_638_);
lean_inc(v_toSeq_637_);
lean_inc(v_toFunctor_636_);
lean_dec(v_toApplicative_635_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_730_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___f_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___f_646_; lean_object* v___x_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___x_652_; 
v___f_643_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_644_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref(v_toFunctor_636_);
v___f_645_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_645_, 0, v_toFunctor_636_);
v___f_646_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_646_, 0, v_toFunctor_636_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___f_645_);
lean_ctor_set(v___x_647_, 1, v___f_646_);
v___f_648_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_648_, 0, v_toSeqRight_639_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_649_, 0, v_toSeqLeft_638_);
v___f_650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_650_, 0, v_toSeq_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v___f_648_);
lean_ctor_set(v___x_641_, 3, v___f_649_);
lean_ctor_set(v___x_641_, 2, v___f_650_);
lean_ctor_set(v___x_641_, 1, v___f_643_);
lean_ctor_set(v___x_641_, 0, v___x_647_);
v___x_652_ = v___x_641_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___f_643_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v___f_650_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v___f_649_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v___f_648_);
v___x_652_ = v_reuseFailAlloc_729_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_toApplicative_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_727_; 
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___f_644_);
v___x_654_ = l_ReaderT_instMonad___redArg(v___x_653_);
v_toApplicative_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v___x_654_, 1);
lean_dec(v_unused_728_);
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_727_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_toApplicative_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_727_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_toFunctor_659_; lean_object* v_toSeq_660_; lean_object* v_toSeqLeft_661_; lean_object* v_toSeqRight_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_725_; 
v_toFunctor_659_ = lean_ctor_get(v_toApplicative_655_, 0);
v_toSeq_660_ = lean_ctor_get(v_toApplicative_655_, 2);
v_toSeqLeft_661_ = lean_ctor_get(v_toApplicative_655_, 3);
v_toSeqRight_662_ = lean_ctor_get(v_toApplicative_655_, 4);
v_isSharedCheck_725_ = !lean_is_exclusive(v_toApplicative_655_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_toApplicative_655_, 1);
lean_dec(v_unused_726_);
v___x_664_ = v_toApplicative_655_;
v_isShared_665_ = v_isSharedCheck_725_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_toSeqRight_662_);
lean_inc(v_toSeqLeft_661_);
lean_inc(v_toSeq_660_);
lean_inc(v_toFunctor_659_);
lean_dec(v_toApplicative_655_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_725_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___f_669_; lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_675_; 
v___f_666_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_659_);
v___f_668_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_668_, 0, v_toFunctor_659_);
v___f_669_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_669_, 0, v_toFunctor_659_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___f_668_);
lean_ctor_set(v___x_670_, 1, v___f_669_);
v___f_671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_671_, 0, v_toSeqRight_662_);
v___f_672_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_672_, 0, v_toSeqLeft_661_);
v___f_673_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_673_, 0, v_toSeq_660_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v___f_671_);
lean_ctor_set(v___x_664_, 3, v___f_672_);
lean_ctor_set(v___x_664_, 2, v___f_673_);
lean_ctor_set(v___x_664_, 1, v___f_666_);
lean_ctor_set(v___x_664_, 0, v___x_670_);
v___x_675_ = v___x_664_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___f_666_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v___f_673_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v___f_672_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v___f_671_);
v___x_675_ = v_reuseFailAlloc_724_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___f_667_);
lean_ctor_set(v___x_657_, 0, v___x_675_);
v___x_677_ = v___x_657_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___f_667_);
v___x_677_ = v_reuseFailAlloc_723_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v_toApplicative_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_721_; 
v_toApplicative_678_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_634_, 1);
lean_dec(v_unused_722_);
v___x_680_ = v___x_634_;
v_isShared_681_ = v_isSharedCheck_721_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_toApplicative_678_);
lean_dec(v___x_634_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_721_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_toFunctor_682_; lean_object* v_toSeq_683_; lean_object* v_toSeqLeft_684_; lean_object* v_toSeqRight_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_719_; 
v_toFunctor_682_ = lean_ctor_get(v_toApplicative_678_, 0);
v_toSeq_683_ = lean_ctor_get(v_toApplicative_678_, 2);
v_toSeqLeft_684_ = lean_ctor_get(v_toApplicative_678_, 3);
v_toSeqRight_685_ = lean_ctor_get(v_toApplicative_678_, 4);
v_isSharedCheck_719_ = !lean_is_exclusive(v_toApplicative_678_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_toApplicative_678_, 1);
lean_dec(v_unused_720_);
v___x_687_ = v_toApplicative_678_;
v_isShared_688_ = v_isSharedCheck_719_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_toSeqRight_685_);
lean_inc(v_toSeqLeft_684_);
lean_inc(v_toSeq_683_);
lean_inc(v_toFunctor_682_);
lean_dec(v_toApplicative_678_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_719_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___f_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___x_696_; 
lean_inc_ref(v_toFunctor_682_);
v___f_689_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_689_, 0, v_toFunctor_682_);
v___f_690_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_690_, 0, v_toFunctor_682_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___f_689_);
lean_ctor_set(v___x_691_, 1, v___f_690_);
v___f_692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_692_, 0, v_toSeqRight_685_);
v___f_693_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_693_, 0, v_toSeqLeft_684_);
v___f_694_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_694_, 0, v_toSeq_683_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 4, v___f_692_);
lean_ctor_set(v___x_687_, 3, v___f_693_);
lean_ctor_set(v___x_687_, 2, v___f_694_);
lean_ctor_set(v___x_687_, 1, v___f_643_);
lean_ctor_set(v___x_687_, 0, v___x_691_);
v___x_696_ = v___x_687_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___f_643_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v___f_694_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v___f_693_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v___f_692_);
v___x_696_ = v_reuseFailAlloc_718_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___f_644_);
lean_ctor_set(v___x_680_, 0, v___x_696_);
v___x_698_ = v___x_680_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___f_644_);
v___x_698_ = v_reuseFailAlloc_717_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_toMonadRef_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_toApplicative_708_; lean_object* v_toBind_709_; lean_object* v_toPure_710_; lean_object* v_liftWith_711_; lean_object* v_restoreM_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_699_ = l_ReaderT_instMonad___redArg(v___x_698_);
v___x_700_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_700_, 0, lean_box(0));
lean_closure_set(v___x_700_, 1, lean_box(0));
lean_closure_set(v___x_700_, 2, v___x_699_);
v___x_701_ = l_instMonadControlTOfPure___redArg(v___x_700_);
v___x_702_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_703_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18);
v_toMonadRef_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_ref(v_toMonadRef_704_);
v___x_705_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_677_);
v___x_706_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_705_, v___x_677_);
v___x_707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_707_, 0, v___x_702_);
lean_ctor_set(v___x_707_, 1, v_toMonadRef_704_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
v_toApplicative_708_ = lean_ctor_get(v_inst_628_, 0);
lean_inc_ref(v_toApplicative_708_);
v_toBind_709_ = lean_ctor_get(v_inst_628_, 1);
lean_inc(v_toBind_709_);
lean_dec_ref(v_inst_628_);
v_toPure_710_ = lean_ctor_get(v_toApplicative_708_, 1);
lean_inc(v_toPure_710_);
lean_dec_ref(v_toApplicative_708_);
v_liftWith_711_ = lean_ctor_get(v_inst_629_, 0);
lean_inc(v_liftWith_711_);
v_restoreM_712_ = lean_ctor_get(v_inst_629_, 1);
lean_inc(v_restoreM_712_);
lean_dec_ref(v_inst_629_);
lean_inc(v_toBind_709_);
v___f_713_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed), 15, 9);
lean_closure_set(v___f_713_, 0, v_goal_631_);
lean_closure_set(v___f_713_, 1, v___x_677_);
lean_closure_set(v___f_713_, 2, v___x_707_);
lean_closure_set(v___f_713_, 3, v_toPure_710_);
lean_closure_set(v___f_713_, 4, v_ident_632_);
lean_closure_set(v___f_713_, 5, v_inst_630_);
lean_closure_set(v___f_713_, 6, v_toBind_709_);
lean_closure_set(v___f_713_, 7, v_k_633_);
lean_closure_set(v___f_713_, 8, v___x_701_);
v___x_714_ = lean_apply_2(v_liftWith_711_, lean_box(0), v___f_713_);
v___x_715_ = lean_apply_1(v_restoreM_712_, lean_box(0));
v___x_716_ = lean_apply_4(v_toBind_709_, lean_box(0), lean_box(0), v___x_714_, v___x_715_);
return v___x_716_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall(lean_object* v_m_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_goal_736_, lean_object* v_ident_737_, lean_object* v_k_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_733_, v_inst_734_, v_inst_735_, v_goal_736_, v_ident_737_, v_k_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(uint8_t v_isZero_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_ref_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_ref_755_ = lean_ctor_get(v___y_752_, 5);
v___x_756_ = l_Lean_SourceInfo_fromRef(v_ref_755_, v_isZero_749_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3));
v___x_759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4));
lean_inc(v___x_756_);
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_756_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
lean_inc(v___x_756_);
v___x_761_ = l_Lean_Syntax_node1(v___x_756_, v___x_758_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node1(v___x_756_, v___x_757_, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed(lean_object* v_isZero_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_isZero_boxed_770_; lean_object* v_res_771_; 
v_isZero_boxed_770_ = lean_unbox(v_isZero_764_);
v_res_771_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(v_isZero_boxed_770_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_goal_775_, lean_object* v___f_776_, lean_object* v_____do__lift_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_772_, v_inst_773_, v_inst_774_, v_goal_775_, v_____do__lift_777_, v___f_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed(lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_n_782_, lean_object* v_k_783_, lean_object* v_g_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(v_inst_779_, v_inst_780_, v_inst_781_, v_n_782_, v_k_783_, v_g_784_);
lean_dec(v_n_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_goal_789_, lean_object* v_n_790_, lean_object* v_k_791_){
_start:
{
lean_object* v_toBind_792_; lean_object* v_zero_793_; uint8_t v_isZero_794_; 
v_toBind_792_ = lean_ctor_get(v_inst_786_, 1);
lean_inc(v_toBind_792_);
v_zero_793_ = lean_unsigned_to_nat(0u);
v_isZero_794_ = lean_nat_dec_eq(v_n_790_, v_zero_793_);
if (v_isZero_794_ == 1)
{
lean_object* v___x_795_; 
lean_dec(v_toBind_792_);
lean_dec(v_inst_788_);
lean_dec_ref(v_inst_787_);
lean_dec_ref(v_inst_786_);
v___x_795_ = lean_apply_1(v_k_791_, v_goal_789_);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v_one_798_; lean_object* v_n_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_796_ = lean_box(v_isZero_794_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_797_, 0, v___x_796_);
v_one_798_ = lean_unsigned_to_nat(1u);
v_n_799_ = lean_nat_sub(v_n_790_, v_one_798_);
lean_inc(v_inst_788_);
lean_inc_ref(v_inst_787_);
lean_inc_ref(v_inst_786_);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_800_, 0, v_inst_786_);
lean_closure_set(v___f_800_, 1, v_inst_787_);
lean_closure_set(v___f_800_, 2, v_inst_788_);
lean_closure_set(v___f_800_, 3, v_n_799_);
lean_closure_set(v___f_800_, 4, v_k_791_);
lean_inc(v_inst_788_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2), 6, 5);
lean_closure_set(v___f_801_, 0, v_inst_786_);
lean_closure_set(v___f_801_, 1, v_inst_787_);
lean_closure_set(v___f_801_, 2, v_inst_788_);
lean_closure_set(v___f_801_, 3, v_goal_789_);
lean_closure_set(v___f_801_, 4, v___f_800_);
v___x_802_ = lean_apply_2(v_inst_788_, lean_box(0), v___f_797_);
v___x_803_ = lean_apply_4(v_toBind_792_, lean_box(0), lean_box(0), v___x_802_, v___f_801_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_n_807_, lean_object* v_k_808_, lean_object* v_g_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_804_, v_inst_805_, v_inst_806_, v_g_809_, v_n_807_, v_k_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___boxed(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_goal_814_, lean_object* v_n_815_, lean_object* v_k_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_811_, v_inst_812_, v_inst_813_, v_goal_814_, v_n_815_, v_k_816_);
lean_dec(v_n_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(lean_object* v_m_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_goal_822_, lean_object* v_n_823_, lean_object* v_k_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_819_, v_inst_820_, v_inst_821_, v_goal_822_, v_n_823_, v_k_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___boxed(lean_object* v_m_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_goal_830_, lean_object* v_n_831_, lean_object* v_k_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(v_m_826_, v_inst_827_, v_inst_828_, v_inst_829_, v_goal_830_, v_n_831_, v_k_832_);
lean_dec(v_n_831_);
return v_res_833_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10));
v___x_863_ = l_String_toRawSubstring_x27(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0));
v___x_878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_874_);
v___x_879_ = l_Lean_Syntax_isOfKind(v_x_874_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v_a_875_);
lean_dec(v_x_874_);
v___x_880_ = lean_box(1);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_a_876_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = l_Lean_Syntax_getArg(v_x_874_, v___x_883_);
lean_dec(v_x_874_);
v___x_885_ = lean_unsigned_to_nat(2u);
v___x_886_ = l_Lean_Syntax_getNumArgs(v___x_884_);
v___x_887_ = lean_nat_dec_le(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; 
lean_dec(v___x_886_);
lean_inc(v___x_884_);
v___x_888_ = l_Lean_Syntax_matchesNull(v___x_884_, v___x_883_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v___x_884_);
lean_dec_ref(v_a_875_);
v___x_889_ = lean_box(1);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_a_876_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = l_Lean_Syntax_getArg(v___x_884_, v___x_882_);
lean_dec(v___x_884_);
v___x_892_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_891_);
v___x_893_ = l_Lean_Syntax_isOfKind(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
lean_dec(v___x_891_);
lean_dec_ref(v_a_875_);
v___x_894_ = l_Lean_Macro_throwUnsupported___redArg(v_a_876_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = l_Lean_Syntax_getArg(v___x_891_, v___x_882_);
lean_dec(v___x_891_);
v___x_896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_895_);
v___x_897_ = l_Lean_Syntax_isOfKind(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v_quotContext_898_; lean_object* v_currMacroScope_899_; lean_object* v_ref_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_quotContext_898_ = lean_ctor_get(v_a_875_, 1);
lean_inc(v_quotContext_898_);
v_currMacroScope_899_ = lean_ctor_get(v_a_875_, 2);
lean_inc(v_currMacroScope_899_);
v_ref_900_ = lean_ctor_get(v_a_875_, 5);
lean_inc(v_ref_900_);
lean_dec_ref(v_a_875_);
v___x_901_ = l_Lean_SourceInfo_fromRef(v_ref_900_, v___x_897_);
lean_dec(v_ref_900_);
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc(v___x_901_);
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___x_877_);
v___x_905_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
v___x_906_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
v___x_908_ = l_Lean_addMacroScope(v_quotContext_898_, v___x_907_, v_currMacroScope_899_);
v___x_909_ = lean_box(0);
lean_inc(v___x_901_);
v___x_910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_910_, 0, v___x_901_);
lean_ctor_set(v___x_910_, 1, v___x_906_);
lean_ctor_set(v___x_910_, 2, v___x_908_);
lean_ctor_set(v___x_910_, 3, v___x_909_);
lean_inc_ref(v___x_910_);
lean_inc(v___x_901_);
v___x_911_ = l_Lean_Syntax_node1(v___x_901_, v___x_905_, v___x_910_);
lean_inc(v___x_901_);
v___x_912_ = l_Lean_Syntax_node1(v___x_901_, v___x_896_, v___x_911_);
lean_inc(v___x_901_);
v___x_913_ = l_Lean_Syntax_node1(v___x_901_, v___x_892_, v___x_912_);
lean_inc(v___x_901_);
v___x_914_ = l_Lean_Syntax_node1(v___x_901_, v___x_903_, v___x_913_);
lean_inc(v___x_901_);
v___x_915_ = l_Lean_Syntax_node2(v___x_901_, v___x_878_, v___x_904_, v___x_914_);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
lean_inc(v___x_901_);
v___x_917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_901_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
lean_inc(v___x_901_);
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_901_);
lean_ctor_set(v___x_920_, 1, v___x_918_);
v___x_921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
lean_inc(v___x_901_);
v___x_922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_901_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
lean_inc(v___x_901_);
v___x_923_ = l_Lean_Syntax_node4(v___x_901_, v___x_919_, v___x_920_, v___x_910_, v___x_922_, v___x_895_);
lean_inc(v___x_901_);
v___x_924_ = l_Lean_Syntax_node3(v___x_901_, v___x_903_, v___x_915_, v___x_917_, v___x_923_);
v___x_925_ = l_Lean_Syntax_node1(v___x_901_, v___x_902_, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v_a_876_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = l_Lean_Syntax_getArg(v___x_895_, v___x_882_);
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
v___x_929_ = l_Lean_Syntax_isOfKind(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v_quotContext_930_; lean_object* v_currMacroScope_931_; lean_object* v_ref_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_quotContext_930_ = lean_ctor_get(v_a_875_, 1);
lean_inc(v_quotContext_930_);
v_currMacroScope_931_ = lean_ctor_get(v_a_875_, 2);
lean_inc(v_currMacroScope_931_);
v_ref_932_ = lean_ctor_get(v_a_875_, 5);
lean_inc(v_ref_932_);
lean_dec_ref(v_a_875_);
v___x_933_ = l_Lean_SourceInfo_fromRef(v_ref_932_, v___x_929_);
lean_dec(v_ref_932_);
v___x_934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc(v___x_933_);
v___x_936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_933_);
lean_ctor_set(v___x_936_, 1, v___x_877_);
v___x_937_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
v___x_939_ = l_Lean_addMacroScope(v_quotContext_930_, v___x_938_, v_currMacroScope_931_);
v___x_940_ = lean_box(0);
lean_inc(v___x_933_);
v___x_941_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_941_, 0, v___x_933_);
lean_ctor_set(v___x_941_, 1, v___x_937_);
lean_ctor_set(v___x_941_, 2, v___x_939_);
lean_ctor_set(v___x_941_, 3, v___x_940_);
lean_inc_ref(v___x_941_);
lean_inc(v___x_933_);
v___x_942_ = l_Lean_Syntax_node1(v___x_933_, v___x_928_, v___x_941_);
lean_inc(v___x_933_);
v___x_943_ = l_Lean_Syntax_node1(v___x_933_, v___x_896_, v___x_942_);
lean_inc(v___x_933_);
v___x_944_ = l_Lean_Syntax_node1(v___x_933_, v___x_892_, v___x_943_);
lean_inc(v___x_933_);
v___x_945_ = l_Lean_Syntax_node1(v___x_933_, v___x_935_, v___x_944_);
lean_inc(v___x_933_);
v___x_946_ = l_Lean_Syntax_node2(v___x_933_, v___x_878_, v___x_936_, v___x_945_);
v___x_947_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
lean_inc(v___x_933_);
v___x_948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_933_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_950_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
lean_inc(v___x_933_);
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_933_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
lean_inc(v___x_933_);
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_933_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
lean_inc(v___x_933_);
v___x_954_ = l_Lean_Syntax_node4(v___x_933_, v___x_950_, v___x_951_, v___x_941_, v___x_953_, v___x_895_);
lean_inc(v___x_933_);
v___x_955_ = l_Lean_Syntax_node3(v___x_933_, v___x_935_, v___x_946_, v___x_948_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node1(v___x_933_, v___x_934_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_876_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; 
lean_dec(v___x_895_);
lean_dec_ref(v_a_875_);
v___x_958_ = l_Lean_Macro_throwUnsupported___redArg(v_a_876_);
return v___x_958_;
}
}
}
}
}
else
{
lean_object* v_ref_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_pats_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_ref_959_ = lean_ctor_get(v_a_875_, 5);
lean_inc(v_ref_959_);
lean_dec_ref(v_a_875_);
v___x_960_ = l_Lean_Syntax_getArg(v___x_884_, v___x_882_);
v___x_961_ = l_Lean_Syntax_getArg(v___x_884_, v___x_883_);
v___x_962_ = l_Lean_Syntax_getArgs(v___x_884_);
lean_dec(v___x_884_);
v___x_963_ = l_Array_extract___redArg(v___x_962_, v___x_885_, v___x_886_);
lean_dec_ref(v___x_962_);
v___x_964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
v___x_965_ = lean_box(2);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_964_);
lean_ctor_set(v___x_966_, 2, v___x_963_);
v_pats_967_ = l_Lean_Syntax_getArgs(v___x_966_);
lean_dec_ref(v___x_966_);
v___x_968_ = 0;
v___x_969_ = l_Lean_SourceInfo_fromRef(v_ref_959_, v___x_968_);
lean_dec(v_ref_959_);
v___x_970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
lean_inc(v___x_969_);
v___x_971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_877_);
lean_inc(v___x_969_);
v___x_972_ = l_Lean_Syntax_node1(v___x_969_, v___x_964_, v___x_960_);
lean_inc_ref(v___x_971_);
lean_inc(v___x_969_);
v___x_973_ = l_Lean_Syntax_node2(v___x_969_, v___x_878_, v___x_971_, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
lean_inc(v___x_969_);
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_969_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Array_mkArray1___redArg(v___x_961_);
v___x_977_ = l_Array_append___redArg(v___x_976_, v_pats_967_);
lean_dec_ref(v_pats_967_);
lean_inc(v___x_969_);
v___x_978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_978_, 0, v___x_969_);
lean_ctor_set(v___x_978_, 1, v___x_964_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
lean_inc(v___x_969_);
v___x_979_ = l_Lean_Syntax_node2(v___x_969_, v___x_878_, v___x_971_, v___x_978_);
lean_inc(v___x_969_);
v___x_980_ = l_Lean_Syntax_node3(v___x_969_, v___x_964_, v___x_973_, v___x_975_, v___x_979_);
v___x_981_ = l_Lean_Syntax_node1(v___x_969_, v___x_970_, v___x_980_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_a_876_);
return v___x_982_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_box(0);
v___x_984_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___boxed(lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(lean_object* v_00_u03b1_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___boxed(lean_object* v_00_u03b1_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(v_00_u03b1_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_apply_9(v_x_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed(lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(v_x_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(lean_object* v_mvarId_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1046_, 0, v_x_1036_);
lean_closure_set(v___f_1046_, 1, v___y_1037_);
lean_closure_set(v___f_1046_, 2, v___y_1038_);
lean_closure_set(v___f_1046_, 3, v___y_1039_);
lean_closure_set(v___f_1046_, 4, v___y_1040_);
v___x_1047_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1035_, v___f_1046_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1047_) == 0)
{
return v___x_1047_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___boxed(lean_object* v_mvarId_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1056_, v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(lean_object* v_00_u03b1_1068_, lean_object* v_mvarId_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1069_, v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_mvarId_1082_, lean_object* v_x_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(v_00_u03b1_1081_, v_mvarId_1082_, v_x_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(lean_object* v_val_1094_, lean_object* v_newGoal_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1095_);
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1105_, v___x_1106_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1119_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1112_ = lean_st_ref_take(v_val_1094_);
v___x_1113_ = l_Lean_Expr_mvarId_x21(v_a_1108_);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1112_);
v___x_1115_ = lean_st_ref_set(v_val_1094_, v___x_1114_);
if (v_isShared_1111_ == 0)
{
v___x_1117_ = v___x_1110_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1108_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed(lean_object* v_val_1120_, lean_object* v_newGoal_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(v_val_1120_, v_newGoal_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v_val_1120_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v_ks_1136_; lean_object* v_vs_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1161_; 
v_ks_1136_ = lean_ctor_get(v_x_1132_, 0);
v_vs_1137_ = lean_ctor_get(v_x_1132_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1139_ = v_x_1132_;
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_vs_1137_);
lean_inc(v_ks_1136_);
lean_dec(v_x_1132_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_array_get_size(v_ks_1136_);
v___x_1142_ = lean_nat_dec_lt(v_x_1133_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_dec(v_x_1133_);
v___x_1143_ = lean_array_push(v_ks_1136_, v_x_1134_);
v___x_1144_ = lean_array_push(v_vs_1137_, v_x_1135_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1144_);
lean_ctor_set(v___x_1139_, 0, v___x_1143_);
v___x_1146_ = v___x_1139_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
else
{
lean_object* v_k_x27_1148_; uint8_t v___x_1149_; 
v_k_x27_1148_ = lean_array_fget_borrowed(v_ks_1136_, v_x_1133_);
v___x_1149_ = l_Lean_instBEqMVarId_beq(v_x_1134_, v_k_x27_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1151_; 
if (v_isShared_1140_ == 0)
{
v___x_1151_ = v___x_1139_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_ks_1136_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_vs_1137_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_x_1133_, v___x_1152_);
lean_dec(v_x_1133_);
v_x_1132_ = v___x_1151_;
v_x_1133_ = v___x_1153_;
goto _start;
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = lean_array_fset(v_ks_1136_, v_x_1133_, v_x_1134_);
v___x_1157_ = lean_array_fset(v_vs_1137_, v_x_1133_, v_x_1135_);
lean_dec(v_x_1133_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1157_);
lean_ctor_set(v___x_1139_, 0, v___x_1156_);
v___x_1159_ = v___x_1139_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_n_1162_, lean_object* v_k_1163_, lean_object* v_v_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_n_1162_, v___x_1165_, v_k_1163_, v_v_1164_);
return v___x_1166_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; 
v___x_1167_ = ((size_t)5ULL);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_shift_left(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; 
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0);
v___x_1172_ = lean_usize_sub(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(lean_object* v_x_1174_, size_t v_x_1175_, size_t v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_es_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v_j_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_es_1179_ = lean_ctor_get(v_x_1174_, 0);
v___x_1180_ = ((size_t)5ULL);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1);
v___x_1183_ = lean_usize_land(v_x_1175_, v___x_1182_);
v_j_1184_ = lean_usize_to_nat(v___x_1183_);
v___x_1185_ = lean_array_get_size(v_es_1179_);
v___x_1186_ = lean_nat_dec_lt(v_j_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_j_1184_);
lean_dec(v_x_1178_);
lean_dec(v_x_1177_);
return v_x_1174_;
}
else
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1223_; 
lean_inc_ref(v_es_1179_);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_x_1174_, 0);
lean_dec(v_unused_1224_);
v___x_1188_ = v_x_1174_;
v_isShared_1189_ = v_isSharedCheck_1223_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_x_1174_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1223_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_xs_x27_1192_; lean_object* v___y_1194_; 
v_v_1190_ = lean_array_fget(v_es_1179_, v_j_1184_);
v___x_1191_ = lean_box(0);
v_xs_x27_1192_ = lean_array_fset(v_es_1179_, v_j_1184_, v___x_1191_);
switch(lean_obj_tag(v_v_1190_))
{
case 0:
{
lean_object* v_key_1199_; lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_key_1199_ = lean_ctor_get(v_v_1190_, 0);
v_val_1200_ = lean_ctor_get(v_v_1190_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v_v_1190_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_inc(v_key_1199_);
lean_dec(v_v_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_instBEqMVarId_beq(v_x_1177_, v_key_1199_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1202_);
v___x_1205_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1199_, v_val_1200_, v_x_1177_, v_x_1178_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
v___y_1194_ = v___x_1206_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1208_; 
lean_dec(v_val_1200_);
lean_dec(v_key_1199_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v_x_1178_);
lean_ctor_set(v___x_1202_, 0, v_x_1177_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_x_1177_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_x_1178_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v___y_1194_ = v___x_1208_;
goto v___jp_1193_;
}
}
}
}
case 1:
{
lean_object* v_node_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1221_; 
v_node_1211_ = lean_ctor_get(v_v_1190_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1213_ = v_v_1190_;
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_node_1211_);
lean_dec(v_v_1190_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1215_ = lean_usize_shift_right(v_x_1175_, v___x_1180_);
v___x_1216_ = lean_usize_add(v_x_1176_, v___x_1181_);
v___x_1217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_node_1211_, v___x_1215_, v___x_1216_, v_x_1177_, v_x_1178_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1217_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v___y_1194_ = v___x_1219_;
goto v___jp_1193_;
}
}
}
default: 
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_x_1177_);
lean_ctor_set(v___x_1222_, 1, v_x_1178_);
v___y_1194_ = v___x_1222_;
goto v___jp_1193_;
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_array_fset(v_xs_x27_1192_, v_j_1184_, v___y_1194_);
lean_dec(v_j_1184_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1195_);
v___x_1197_ = v___x_1188_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
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
}
else
{
lean_object* v_ks_1225_; lean_object* v_vs_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1246_; 
v_ks_1225_ = lean_ctor_get(v_x_1174_, 0);
v_vs_1226_ = lean_ctor_get(v_x_1174_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1228_ = v_x_1174_;
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_vs_1226_);
lean_inc(v_ks_1225_);
lean_dec(v_x_1174_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_ks_1225_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_vs_1226_);
v___x_1231_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v_newNode_1232_; uint8_t v___y_1234_; size_t v___x_1240_; uint8_t v___x_1241_; 
v_newNode_1232_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v___x_1231_, v_x_1177_, v_x_1178_);
v___x_1240_ = ((size_t)7ULL);
v___x_1241_ = lean_usize_dec_le(v___x_1240_, v_x_1176_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1242_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1232_);
v___x_1243_ = lean_unsigned_to_nat(4u);
v___x_1244_ = lean_nat_dec_lt(v___x_1242_, v___x_1243_);
lean_dec(v___x_1242_);
v___y_1234_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
v___y_1234_ = v___x_1241_;
goto v___jp_1233_;
}
v___jp_1233_:
{
if (v___y_1234_ == 0)
{
lean_object* v_ks_1235_; lean_object* v_vs_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_ks_1235_ = lean_ctor_get(v_newNode_1232_, 0);
lean_inc_ref(v_ks_1235_);
v_vs_1236_ = lean_ctor_get(v_newNode_1232_, 1);
lean_inc_ref(v_vs_1236_);
lean_dec_ref(v_newNode_1232_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2);
v___x_1239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_x_1176_, v_ks_1235_, v_vs_1236_, v___x_1237_, v___x_1238_);
lean_dec_ref(v_vs_1236_);
lean_dec_ref(v_ks_1235_);
return v___x_1239_;
}
else
{
return v_newNode_1232_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(size_t v_depth_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_i_1250_, lean_object* v_entries_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_keys_1248_);
v___x_1253_ = lean_nat_dec_lt(v_i_1250_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v_i_1250_);
return v_entries_1251_;
}
else
{
lean_object* v_k_1254_; lean_object* v_v_1255_; uint64_t v___x_1256_; size_t v_h_1257_; size_t v___x_1258_; lean_object* v___x_1259_; size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v_h_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_k_1254_ = lean_array_fget_borrowed(v_keys_1248_, v_i_1250_);
v_v_1255_ = lean_array_fget_borrowed(v_vals_1249_, v_i_1250_);
v___x_1256_ = l_Lean_instHashableMVarId_hash(v_k_1254_);
v_h_1257_ = lean_uint64_to_usize(v___x_1256_);
v___x_1258_ = ((size_t)5ULL);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_sub(v_depth_1247_, v___x_1260_);
v___x_1262_ = lean_usize_mul(v___x_1258_, v___x_1261_);
v_h_1263_ = lean_usize_shift_right(v_h_1257_, v___x_1262_);
v___x_1264_ = lean_nat_add(v_i_1250_, v___x_1259_);
lean_dec(v_i_1250_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
v___x_1265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_entries_1251_, v_h_1263_, v_depth_1247_, v_k_1254_, v_v_1255_);
v_i_1250_ = v___x_1264_;
v_entries_1251_ = v___x_1265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_depth_1267_, lean_object* v_keys_1268_, lean_object* v_vals_1269_, lean_object* v_i_1270_, lean_object* v_entries_1271_){
_start:
{
size_t v_depth_boxed_1272_; lean_object* v_res_1273_; 
v_depth_boxed_1272_ = lean_unbox_usize(v_depth_1267_);
lean_dec(v_depth_1267_);
v_res_1273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_boxed_1272_, v_keys_1268_, v_vals_1269_, v_i_1270_, v_entries_1271_);
lean_dec_ref(v_vals_1269_);
lean_dec_ref(v_keys_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
size_t v_x_20210__boxed_1279_; size_t v_x_20211__boxed_1280_; lean_object* v_res_1281_; 
v_x_20210__boxed_1279_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_x_20211__boxed_1280_ = lean_unbox_usize(v_x_1276_);
lean_dec(v_x_1276_);
v_res_1281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1274_, v_x_20210__boxed_1279_, v_x_20211__boxed_1280_, v_x_1277_, v_x_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
uint64_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = l_Lean_instHashableMVarId_hash(v_x_1283_);
v___x_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1282_, v___x_1286_, v___x_1287_, v_x_1283_, v_x_1284_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(lean_object* v_mvarId_1289_, lean_object* v_val_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_mctx_1294_; lean_object* v_cache_1295_; lean_object* v_zetaDeltaFVarIds_1296_; lean_object* v_postponed_1297_; lean_object* v_diag_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1325_; 
v___x_1293_ = lean_st_ref_take(v___y_1291_);
v_mctx_1294_ = lean_ctor_get(v___x_1293_, 0);
v_cache_1295_ = lean_ctor_get(v___x_1293_, 1);
v_zetaDeltaFVarIds_1296_ = lean_ctor_get(v___x_1293_, 2);
v_postponed_1297_ = lean_ctor_get(v___x_1293_, 3);
v_diag_1298_ = lean_ctor_get(v___x_1293_, 4);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1300_ = v___x_1293_;
v_isShared_1301_ = v_isSharedCheck_1325_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_diag_1298_);
lean_inc(v_postponed_1297_);
lean_inc(v_zetaDeltaFVarIds_1296_);
lean_inc(v_cache_1295_);
lean_inc(v_mctx_1294_);
lean_dec(v___x_1293_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1325_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_depth_1302_; lean_object* v_levelAssignDepth_1303_; lean_object* v_mvarCounter_1304_; lean_object* v_lDepth_1305_; lean_object* v_decls_1306_; lean_object* v_userNames_1307_; lean_object* v_lAssignment_1308_; lean_object* v_eAssignment_1309_; lean_object* v_dAssignment_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1324_; 
v_depth_1302_ = lean_ctor_get(v_mctx_1294_, 0);
v_levelAssignDepth_1303_ = lean_ctor_get(v_mctx_1294_, 1);
v_mvarCounter_1304_ = lean_ctor_get(v_mctx_1294_, 2);
v_lDepth_1305_ = lean_ctor_get(v_mctx_1294_, 3);
v_decls_1306_ = lean_ctor_get(v_mctx_1294_, 4);
v_userNames_1307_ = lean_ctor_get(v_mctx_1294_, 5);
v_lAssignment_1308_ = lean_ctor_get(v_mctx_1294_, 6);
v_eAssignment_1309_ = lean_ctor_get(v_mctx_1294_, 7);
v_dAssignment_1310_ = lean_ctor_get(v_mctx_1294_, 8);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_mctx_1294_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1312_ = v_mctx_1294_;
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_dAssignment_1310_);
lean_inc(v_eAssignment_1309_);
lean_inc(v_lAssignment_1308_);
lean_inc(v_userNames_1307_);
lean_inc(v_decls_1306_);
lean_inc(v_lDepth_1305_);
lean_inc(v_mvarCounter_1304_);
lean_inc(v_levelAssignDepth_1303_);
lean_inc(v_depth_1302_);
lean_dec(v_mctx_1294_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_eAssignment_1309_, v_mvarId_1289_, v_val_1290_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 7, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_depth_1302_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_levelAssignDepth_1303_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_mvarCounter_1304_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_lDepth_1305_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_decls_1306_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_userNames_1307_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v_lAssignment_1308_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 8, v_dAssignment_1310_);
v___x_1316_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1316_);
v___x_1318_ = v___x_1300_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_cache_1295_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_zetaDeltaFVarIds_1296_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_postponed_1297_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_diag_1298_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_st_ref_set(v___y_1291_, v___x_1318_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(lean_object* v_mvarId_1326_, lean_object* v_val_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_1326_, v_val_1327_, v___y_1328_);
lean_dec(v___y_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_k_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_apply_6(v_k_1331_, v_b_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, lean_box(0));
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_k_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_1339_, v_b_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(lean_object* v_name_1347_, uint8_t v_bi_1348_, lean_object* v_type_1349_, lean_object* v_k_1350_, uint8_t v_kind_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___f_1357_; lean_object* v___x_1358_; 
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1357_, 0, v_k_1350_);
v___x_1358_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1347_, v_bi_1348_, v_type_1349_, v___f_1357_, v_kind_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1358_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1358_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_name_1375_, lean_object* v_bi_1376_, lean_object* v_type_1377_, lean_object* v_k_1378_, lean_object* v_kind_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v_bi_boxed_1385_; uint8_t v_kind_boxed_1386_; lean_object* v_res_1387_; 
v_bi_boxed_1385_ = lean_unbox(v_bi_1376_);
v_kind_boxed_1386_ = lean_unbox(v_kind_1379_);
v_res_1387_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1375_, v_bi_boxed_1385_, v_type_1377_, v_k_1378_, v_kind_boxed_1386_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(lean_object* v_name_1388_, lean_object* v_type_1389_, lean_object* v_k_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = 0;
v___x_1397_ = 0;
v___x_1398_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1388_, v___x_1396_, v_type_1389_, v_k_1390_, v___x_1397_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(lean_object* v_name_1399_, lean_object* v_type_1400_, lean_object* v_k_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_1399_, v_type_1400_, v_k_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(lean_object* v_msgData_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v_env_1415_; lean_object* v___x_1416_; lean_object* v_mctx_1417_; lean_object* v_lctx_1418_; lean_object* v_options_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1414_ = lean_st_ref_get(v___y_1412_);
v_env_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc_ref(v_env_1415_);
lean_dec(v___x_1414_);
v___x_1416_ = lean_st_ref_get(v___y_1410_);
v_mctx_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_mctx_1417_);
lean_dec(v___x_1416_);
v_lctx_1418_ = lean_ctor_get(v___y_1409_, 2);
v_options_1419_ = lean_ctor_get(v___y_1411_, 2);
lean_inc_ref(v_options_1419_);
lean_inc_ref(v_lctx_1418_);
v___x_1420_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1420_, 0, v_env_1415_);
lean_ctor_set(v___x_1420_, 1, v_mctx_1417_);
lean_ctor_set(v___x_1420_, 2, v_lctx_1418_);
lean_ctor_set(v___x_1420_, 3, v_options_1419_);
v___x_1421_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v_msgData_1408_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(lean_object* v_msg_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_ref_1436_; lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_ref_1436_ = lean_ctor_get(v___y_1433_, 5);
v___x_1437_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msg_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_inc(v_ref_1436_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_ref_1436_);
lean_ctor_set(v___x_1442_, 1, v_a_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
lean_ctor_set(v___x_1440_, 0, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(lean_object* v___x_1454_, lean_object* v_ident_1455_, uint8_t v___x_1456_, lean_object* v_hyps_1457_, lean_object* v___x_1458_, lean_object* v_target_1459_, lean_object* v_u_1460_, lean_object* v_k_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v_s_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_lctx_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_lctx_1472_ = lean_ctor_get(v___y_1467_, 2);
lean_inc_ref(v___x_1454_);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1454_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc_ref(v_s_1466_);
lean_inc_ref(v_lctx_1472_);
v___x_1474_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_1455_, v_lctx_1472_, v_s_1466_, v___x_1473_, v___x_1456_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v___x_1474_);
lean_inc_ref(v_s_1466_);
lean_inc_ref(v_hyps_1457_);
v___x_1475_ = l_Lean_Expr_app___override(v_hyps_1457_, v_s_1466_);
lean_inc_ref(v___x_1458_);
v___x_1476_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_1458_, v___x_1475_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_mk_empty_array_with_capacity(v___x_1477_);
v___x_1479_ = lean_array_push(v___x_1478_, v_s_1466_);
v___x_1480_ = 0;
lean_inc_ref(v_target_1459_);
v___x_1481_ = l_Lean_Expr_betaRev(v_target_1459_, v___x_1479_, v___x_1480_, v___x_1480_);
lean_inc_ref(v___x_1458_);
lean_inc(v_u_1460_);
v___x_1482_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1482_, 0, v_u_1460_);
lean_ctor_set(v___x_1482_, 1, v___x_1458_);
lean_ctor_set(v___x_1482_, 2, v___x_1476_);
lean_ctor_set(v___x_1482_, 3, v___x_1481_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
v___x_1483_ = lean_apply_10(v_k_1461_, v___x_1482_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, lean_box(0));
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = 1;
v___x_1486_ = l_Lean_Meta_mkLambdaFVars(v___x_1479_, v_a_1484_, v___x_1480_, v___x_1456_, v___x_1480_, v___x_1456_, v___x_1485_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec_ref(v___x_1479_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1499_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_u_1460_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_mkConst(v___x_1491_, v___x_1493_);
v___x_1495_ = l_Lean_mkApp5(v___x_1494_, v___x_1458_, v___x_1454_, v_hyps_1457_, v_target_1459_, v_a_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1495_);
v___x_1497_ = v___x_1489_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_dec(v_u_1460_);
lean_dec_ref(v_target_1459_);
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_hyps_1457_);
lean_dec_ref(v___x_1454_);
return v___x_1486_;
}
}
else
{
lean_dec_ref(v___x_1479_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v_u_1460_);
lean_dec_ref(v_target_1459_);
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_hyps_1457_);
lean_dec_ref(v___x_1454_);
return v___x_1483_;
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec_ref(v_s_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec_ref(v_k_1461_);
lean_dec(v_u_1460_);
lean_dec_ref(v_target_1459_);
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_hyps_1457_);
lean_dec_ref(v___x_1454_);
v_a_1500_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1474_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1474_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_1508_ = _args[0];
lean_object* v_ident_1509_ = _args[1];
lean_object* v___x_1510_ = _args[2];
lean_object* v_hyps_1511_ = _args[3];
lean_object* v___x_1512_ = _args[4];
lean_object* v_target_1513_ = _args[5];
lean_object* v_u_1514_ = _args[6];
lean_object* v_k_1515_ = _args[7];
lean_object* v___y_1516_ = _args[8];
lean_object* v___y_1517_ = _args[9];
lean_object* v___y_1518_ = _args[10];
lean_object* v___y_1519_ = _args[11];
lean_object* v_s_1520_ = _args[12];
lean_object* v___y_1521_ = _args[13];
lean_object* v___y_1522_ = _args[14];
lean_object* v___y_1523_ = _args[15];
lean_object* v___y_1524_ = _args[16];
lean_object* v___y_1525_ = _args[17];
_start:
{
uint8_t v___x_20589__boxed_1526_; lean_object* v_res_1527_; 
v___x_20589__boxed_1526_ = lean_unbox(v___x_1510_);
v_res_1527_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_1508_, v_ident_1509_, v___x_20589__boxed_1526_, v_hyps_1511_, v___x_1512_, v_target_1513_, v_u_1514_, v_k_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v_s_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(lean_object* v_goal_1528_, lean_object* v_ident_1529_, lean_object* v_k_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___y_1541_; lean_object* v_u_1550_; lean_object* v_00_u03c3s_1551_; lean_object* v_hyps_1552_; lean_object* v_target_1553_; lean_object* v___x_1554_; 
v_u_1550_ = lean_ctor_get(v_goal_1528_, 0);
lean_inc(v_u_1550_);
v_00_u03c3s_1551_ = lean_ctor_get(v_goal_1528_, 1);
lean_inc_ref(v_00_u03c3s_1551_);
v_hyps_1552_ = lean_ctor_get(v_goal_1528_, 2);
lean_inc_ref(v_hyps_1552_);
v_target_1553_ = lean_ctor_get(v_goal_1528_, 3);
lean_inc_ref(v_target_1553_);
lean_dec_ref(v_goal_1528_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
lean_inc_ref(v_00_u03c3s_1551_);
v___x_1554_ = lean_whnf(v_00_u03c3s_1551_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_1557_ = lean_unsigned_to_nat(3u);
v___x_1558_ = l_Lean_Expr_isAppOfArity(v_a_1555_, v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v_a_1555_);
lean_dec_ref(v_target_1553_);
lean_dec_ref(v_hyps_1552_);
lean_dec(v_u_1550_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_k_1530_);
lean_dec(v_ident_1529_);
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_1560_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_1551_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1561_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
v___y_1541_ = v___x_1562_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
lean_dec_ref(v_00_u03c3s_1551_);
v___x_1563_ = l_Lean_Expr_appFn_x21(v_a_1555_);
v___x_1564_ = l_Lean_Expr_appArg_x21(v___x_1563_);
lean_dec_ref(v___x_1563_);
v___x_1565_ = l_Lean_Expr_appArg_x21(v_a_1555_);
lean_dec(v_a_1555_);
v___x_1566_ = lean_box(v___x_1558_);
lean_inc(v_ident_1529_);
lean_inc_ref(v___x_1564_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1567_, 0, v___x_1564_);
lean_closure_set(v___f_1567_, 1, v_ident_1529_);
lean_closure_set(v___f_1567_, 2, v___x_1566_);
lean_closure_set(v___f_1567_, 3, v_hyps_1552_);
lean_closure_set(v___f_1567_, 4, v___x_1565_);
lean_closure_set(v___f_1567_, 5, v_target_1553_);
lean_closure_set(v___f_1567_, 6, v_u_1550_);
lean_closure_set(v___f_1567_, 7, v_k_1530_);
lean_closure_set(v___f_1567_, 8, v___y_1531_);
lean_closure_set(v___f_1567_, 9, v___y_1532_);
lean_closure_set(v___f_1567_, 10, v___y_1533_);
lean_closure_set(v___f_1567_, 11, v___y_1534_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
lean_inc(v_ident_1529_);
v___x_1569_ = l_Lean_Syntax_isOfKind(v_ident_1529_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_ident_1529_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
v___x_1571_ = l_Lean_Core_mkFreshUserName(v___x_1570_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1572_, v___x_1564_, v___f_1567_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
v___y_1541_ = v___x_1573_;
goto v___jp_1540_;
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___f_1567_);
lean_dec_ref(v___x_1564_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
v_a_1574_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1571_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1571_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = l_Lean_Syntax_getArg(v_ident_1529_, v___x_1582_);
lean_dec(v_ident_1529_);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28));
lean_inc(v___x_1583_);
v___x_1585_ = l_Lean_Syntax_isOfKind(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v___x_1583_);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
v___x_1587_ = l_Lean_Core_mkFreshUserName(v___x_1586_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1588_, v___x_1564_, v___f_1567_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
v___y_1541_ = v___x_1589_;
goto v___jp_1540_;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v___f_1567_);
lean_dec_ref(v___x_1564_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
v_a_1590_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1587_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1587_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Lean_TSyntax_getId(v___x_1583_);
lean_dec(v___x_1583_);
v___x_1599_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v___x_1598_, v___x_1564_, v___f_1567_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
v___y_1541_ = v___x_1599_;
goto v___jp_1540_;
}
}
}
}
else
{
lean_dec_ref(v_target_1553_);
lean_dec_ref(v_hyps_1552_);
lean_dec_ref(v_00_u03c3s_1551_);
lean_dec(v_u_1550_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_k_1530_);
lean_dec(v_ident_1529_);
return v___x_1554_;
}
v___jp_1540_:
{
if (lean_obj_tag(v___y_1541_) == 0)
{
return v___y_1541_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___y_1541_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___y_1541_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___y_1541_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___y_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(lean_object* v_goal_1600_, lean_object* v_ident_1601_, lean_object* v_k_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_1600_, v_ident_1601_, v_k_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(lean_object* v___x_1613_, lean_object* v_snd_1614_, lean_object* v_ident_1615_, lean_object* v_fst_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_st_mk_ref(v___x_1613_);
lean_inc(v___x_1626_);
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1627_, 0, v___x_1626_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
lean_inc(v___y_1618_);
v___x_1628_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_snd_1614_, v_ident_1615_, v___f_1627_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref(v___x_1628_);
v___x_1630_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1616_, v_a_1629_, v___y_1622_);
lean_dec_ref(v___x_1630_);
v___x_1631_ = lean_st_ref_get(v___x_1626_);
lean_dec(v___x_1626_);
v___x_1632_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1631_, v___y_1618_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1618_);
return v___x_1632_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v___x_1626_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1618_);
lean_dec(v_fst_1616_);
v_a_1633_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1628_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1628_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(lean_object* v___x_1641_, lean_object* v_snd_1642_, lean_object* v_ident_1643_, lean_object* v_fst_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(v___x_1641_, v_snd_1642_, v_ident_1643_, v_fst_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(lean_object* v_k_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_apply_10(v_k_1655_, v_b_1660_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, lean_box(0));
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(lean_object* v_k_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v_b_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v_b_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(lean_object* v_name_1679_, lean_object* v_type_1680_, lean_object* v_val_1681_, lean_object* v_k_1682_, uint8_t v_nondep_1683_, uint8_t v_kind_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___f_1694_; lean_object* v___x_1695_; 
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1694_, 0, v_k_1682_);
lean_closure_set(v___f_1694_, 1, v___y_1685_);
lean_closure_set(v___f_1694_, 2, v___y_1686_);
lean_closure_set(v___f_1694_, 3, v___y_1687_);
lean_closure_set(v___f_1694_, 4, v___y_1688_);
v___x_1695_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1679_, v_type_1680_, v_val_1681_, v___f_1694_, v_nondep_1683_, v_kind_1684_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1695_) == 0)
{
return v___x_1695_;
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(lean_object* v_name_1704_, lean_object* v_type_1705_, lean_object* v_val_1706_, lean_object* v_k_1707_, lean_object* v_nondep_1708_, lean_object* v_kind_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v_nondep_boxed_1719_; uint8_t v_kind_boxed_1720_; lean_object* v_res_1721_; 
v_nondep_boxed_1719_ = lean_unbox(v_nondep_1708_);
v_kind_boxed_1720_ = lean_unbox(v_kind_1709_);
v_res_1721_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1704_, v_type_1705_, v_val_1706_, v_k_1707_, v_nondep_boxed_1719_, v_kind_boxed_1720_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v_ngen_1725_; lean_object* v_namePrefix_1726_; lean_object* v_idx_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1756_; 
v___x_1724_ = lean_st_ref_get(v___y_1722_);
v_ngen_1725_ = lean_ctor_get(v___x_1724_, 2);
lean_inc_ref(v_ngen_1725_);
lean_dec(v___x_1724_);
v_namePrefix_1726_ = lean_ctor_get(v_ngen_1725_, 0);
v_idx_1727_ = lean_ctor_get(v_ngen_1725_, 1);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_ngen_1725_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1729_ = v_ngen_1725_;
v_isShared_1730_ = v_isSharedCheck_1756_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_idx_1727_);
lean_inc(v_namePrefix_1726_);
lean_dec(v_ngen_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1756_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v_env_1732_; lean_object* v_nextMacroScope_1733_; lean_object* v_auxDeclNGen_1734_; lean_object* v_traceState_1735_; lean_object* v_cache_1736_; lean_object* v_messages_1737_; lean_object* v_infoState_1738_; lean_object* v_snapshotTasks_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1754_; 
v___x_1731_ = lean_st_ref_take(v___y_1722_);
v_env_1732_ = lean_ctor_get(v___x_1731_, 0);
v_nextMacroScope_1733_ = lean_ctor_get(v___x_1731_, 1);
v_auxDeclNGen_1734_ = lean_ctor_get(v___x_1731_, 3);
v_traceState_1735_ = lean_ctor_get(v___x_1731_, 4);
v_cache_1736_ = lean_ctor_get(v___x_1731_, 5);
v_messages_1737_ = lean_ctor_get(v___x_1731_, 6);
v_infoState_1738_ = lean_ctor_get(v___x_1731_, 7);
v_snapshotTasks_1739_ = lean_ctor_get(v___x_1731_, 8);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1731_, 2);
lean_dec(v_unused_1755_);
v___x_1741_ = v___x_1731_;
v_isShared_1742_ = v_isSharedCheck_1754_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snapshotTasks_1739_);
lean_inc(v_infoState_1738_);
lean_inc(v_messages_1737_);
lean_inc(v_cache_1736_);
lean_inc(v_traceState_1735_);
lean_inc(v_auxDeclNGen_1734_);
lean_inc(v_nextMacroScope_1733_);
lean_inc(v_env_1732_);
lean_dec(v___x_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1754_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_r_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_inc(v_idx_1727_);
lean_inc(v_namePrefix_1726_);
v_r_1743_ = l_Lean_Name_num___override(v_namePrefix_1726_, v_idx_1727_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_idx_1727_, v___x_1744_);
lean_dec(v_idx_1727_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v___x_1745_);
v___x_1747_ = v___x_1729_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_namePrefix_1726_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 2, v___x_1747_);
v___x_1749_ = v___x_1741_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_env_1732_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_nextMacroScope_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_auxDeclNGen_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_traceState_1735_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v_cache_1736_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_messages_1737_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v_infoState_1738_);
lean_ctor_set(v_reuseFailAlloc_1752_, 8, v_snapshotTasks_1739_);
v___x_1749_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_st_ref_set(v___y_1722_, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_r_1743_);
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1757_);
lean_dec(v___y_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(lean_object* v_body_1760_, lean_object* v_u_1761_, lean_object* v_00_u03c3s_1762_, lean_object* v_hyps_1763_, lean_object* v_k_1764_, lean_object* v_val_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_expr_instantiate1(v_body_1760_, v_val_1765_);
v___x_1776_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1776_, 0, v_u_1761_);
lean_ctor_set(v___x_1776_, 1, v_00_u03c3s_1762_);
lean_ctor_set(v___x_1776_, 2, v_hyps_1763_);
lean_ctor_set(v___x_1776_, 3, v___x_1775_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
v___x_1777_ = lean_apply_10(v_k_1764_, v___x_1776_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, lean_box(0));
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_mk_empty_array_with_capacity(v___x_1779_);
v___x_1781_ = lean_array_push(v___x_1780_, v_val_1765_);
v___x_1782_ = 1;
v___x_1783_ = 1;
v___x_1784_ = l_Lean_Meta_mkLetFVars(v___x_1781_, v_a_1778_, v___x_1782_, v___x_1782_, v___x_1783_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___x_1781_);
return v___x_1784_;
}
else
{
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v_val_1765_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(lean_object* v_body_1785_, lean_object* v_u_1786_, lean_object* v_00_u03c3s_1787_, lean_object* v_hyps_1788_, lean_object* v_k_1789_, lean_object* v_val_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_1785_, v_u_1786_, v_00_u03c3s_1787_, v_hyps_1788_, v_k_1789_, v_val_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec_ref(v_body_1785_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(lean_object* v_goal_1808_, lean_object* v_ident_1809_, lean_object* v_k_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_u_1820_; lean_object* v_00_u03c3s_1821_; lean_object* v_hyps_1822_; lean_object* v_target_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1934_; 
v_u_1820_ = lean_ctor_get(v_goal_1808_, 0);
v_00_u03c3s_1821_ = lean_ctor_get(v_goal_1808_, 1);
v_hyps_1822_ = lean_ctor_get(v_goal_1808_, 2);
v_target_1823_ = lean_ctor_get(v_goal_1808_, 3);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_goal_1808_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1825_ = v_goal_1808_;
v_isShared_1826_ = v_isSharedCheck_1934_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_target_1823_);
lean_inc(v_hyps_1822_);
lean_inc(v_00_u03c3s_1821_);
lean_inc(v_u_1820_);
lean_dec(v_goal_1808_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1934_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23));
v___x_1828_ = lean_unsigned_to_nat(3u);
v___x_1829_ = l_Lean_Expr_isAppOfArity(v_target_1823_, v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_del_object(v___x_1825_);
if (lean_obj_tag(v_target_1823_) == 8)
{
lean_object* v_declName_1830_; lean_object* v_type_1831_; lean_object* v_value_1832_; lean_object* v_body_1833_; lean_object* v___f_1834_; lean_object* v_name_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_declName_1830_ = lean_ctor_get(v_target_1823_, 0);
lean_inc(v_declName_1830_);
v_type_1831_ = lean_ctor_get(v_target_1823_, 1);
lean_inc_ref(v_type_1831_);
v_value_1832_ = lean_ctor_get(v_target_1823_, 2);
lean_inc_ref(v_value_1832_);
v_body_1833_ = lean_ctor_get(v_target_1823_, 3);
lean_inc_ref(v_body_1833_);
lean_dec_ref(v_target_1823_);
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed), 15, 5);
lean_closure_set(v___f_1834_, 0, v_body_1833_);
lean_closure_set(v___f_1834_, 1, v_u_1820_);
lean_closure_set(v___f_1834_, 2, v_00_u03c3s_1821_);
lean_closure_set(v___f_1834_, 3, v_hyps_1822_);
lean_closure_set(v___f_1834_, 4, v_k_1810_);
v___x_1847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
lean_inc(v_ident_1809_);
v___x_1848_ = l_Lean_Syntax_isOfKind(v_ident_1809_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec(v_ident_1809_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
v___x_1849_ = l_Lean_Core_mkFreshUserName(v_declName_1830_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v_name_1836_ = v_a_1850_;
v___y_1837_ = v___y_1811_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
v___y_1844_ = v___y_1818_;
goto v___jp_1835_;
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___f_1834_);
lean_dec_ref(v_value_1832_);
lean_dec_ref(v_type_1831_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
v_a_1851_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1849_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1849_);
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
else
{
lean_object* v___x_1859_; lean_object* v_name_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v_name_1860_ = l_Lean_Syntax_getArg(v_ident_1809_, v___x_1859_);
lean_dec(v_ident_1809_);
v___x_1861_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28));
lean_inc(v_name_1860_);
v___x_1862_ = l_Lean_Syntax_isOfKind(v_name_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_dec(v_name_1860_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
v___x_1863_ = l_Lean_Core_mkFreshUserName(v_declName_1830_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v_name_1836_ = v_a_1864_;
v___y_1837_ = v___y_1811_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
v___y_1844_ = v___y_1818_;
goto v___jp_1835_;
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v___f_1834_);
lean_dec_ref(v_value_1832_);
lean_dec_ref(v_type_1831_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
v_a_1865_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1863_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1863_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_declName_1830_);
v___x_1873_ = l_Lean_TSyntax_getId(v_name_1860_);
lean_dec(v_name_1860_);
v_name_1836_ = v___x_1873_;
v___y_1837_ = v___y_1811_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
v___y_1844_ = v___y_1818_;
goto v___jp_1835_;
}
}
v___jp_1835_:
{
uint8_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = 0;
v___x_1846_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1836_, v_type_1831_, v_value_1832_, v___f_1834_, v___x_1829_, v___x_1845_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_hyps_1822_);
lean_dec_ref(v_00_u03c3s_1821_);
lean_dec(v_u_1820_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v_k_1810_);
lean_dec(v_ident_1809_);
v___x_1874_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30);
v___x_1875_ = l_Lean_MessageData_ofExpr(v_target_1823_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1876_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v___x_1877_;
}
}
else
{
lean_object* v___x_1878_; 
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
v___x_1878_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_1809_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v_fst_1880_; lean_object* v_snd_1881_; lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v_hyp_1888_; lean_object* v___x_1889_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v_fst_1880_ = lean_ctor_get(v_a_1879_, 0);
lean_inc(v_fst_1880_);
v_snd_1881_ = lean_ctor_get(v_a_1879_, 1);
lean_inc(v_snd_1881_);
lean_dec(v_a_1879_);
v___x_1882_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1818_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_Expr_appFn_x21(v_target_1823_);
v___x_1885_ = l_Lean_Expr_appFn_x21(v___x_1884_);
v___x_1886_ = l_Lean_Expr_appArg_x21(v___x_1885_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = l_Lean_Expr_appArg_x21(v___x_1884_);
lean_dec_ref(v___x_1884_);
v_hyp_1888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_1888_, 0, v_fst_1880_);
lean_ctor_set(v_hyp_1888_, 1, v_a_1883_);
lean_ctor_set(v_hyp_1888_, 2, v___x_1887_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc_ref(v_hyp_1888_);
lean_inc_ref(v___x_1886_);
v___x_1889_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1881_, v___x_1886_, v_hyp_1888_, v___x_1829_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_H_1890_; lean_object* v___x_1891_; lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v___x_1889_);
v_H_1890_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_1888_);
lean_inc_ref(v_H_1890_);
lean_inc_ref(v_hyps_1822_);
lean_inc_ref(v_00_u03c3s_1821_);
lean_inc(v_u_1820_);
v___x_1891_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_1820_, v_00_u03c3s_1821_, v_hyps_1822_, v_H_1890_);
v_fst_1892_ = lean_ctor_get(v___x_1891_, 0);
v_snd_1893_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1895_ = v___x_1891_;
v_isShared_1896_ = v_isSharedCheck_1917_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snd_1893_);
lean_inc(v_fst_1892_);
lean_dec(v___x_1891_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1917_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_Expr_appArg_x21(v_target_1823_);
lean_dec_ref(v_target_1823_);
lean_inc_ref(v___x_1897_);
lean_inc(v_fst_1892_);
lean_inc(v_u_1820_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 3, v___x_1897_);
lean_ctor_set(v___x_1825_, 2, v_fst_1892_);
v___x_1899_ = v___x_1825_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_u_1820_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_00_u03c3s_1821_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_fst_1892_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_apply_10(v_k_1810_, v___x_1899_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, lean_box(0));
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1915_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0));
v___x_1906_ = lean_box(0);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
lean_ctor_set(v___x_1895_, 1, v___x_1906_);
lean_ctor_set(v___x_1895_, 0, v_u_1820_);
v___x_1908_ = v___x_1895_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_u_1820_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v_prf_1910_; lean_object* v___x_1912_; 
v___x_1909_ = l_Lean_mkConst(v___x_1905_, v___x_1908_);
v_prf_1910_ = l_Lean_mkApp7(v___x_1909_, v___x_1886_, v_fst_1892_, v_hyps_1822_, v_H_1890_, v___x_1897_, v_snd_1893_, v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v_prf_1910_);
v___x_1912_ = v___x_1903_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_prf_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_dec_ref(v___x_1897_);
lean_del_object(v___x_1895_);
lean_dec(v_snd_1893_);
lean_dec(v_fst_1892_);
lean_dec_ref(v_H_1890_);
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_hyps_1822_);
lean_dec(v_u_1820_);
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v_hyp_1888_);
lean_dec_ref(v___x_1886_);
lean_del_object(v___x_1825_);
lean_dec_ref(v_target_1823_);
lean_dec_ref(v_hyps_1822_);
lean_dec_ref(v_00_u03c3s_1821_);
lean_dec(v_u_1820_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v_k_1810_);
v_a_1918_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1889_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1889_);
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
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_del_object(v___x_1825_);
lean_dec_ref(v_target_1823_);
lean_dec_ref(v_hyps_1822_);
lean_dec_ref(v_00_u03c3s_1821_);
lean_dec(v_u_1820_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v_k_1810_);
v_a_1926_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1878_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1878_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(lean_object* v_goal_1935_, lean_object* v_ident_1936_, lean_object* v_k_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_1935_, v_ident_1936_, v_k_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(lean_object* v___x_1948_, lean_object* v_snd_1949_, lean_object* v_ident_1950_, lean_object* v_fst_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_st_mk_ref(v___x_1948_);
lean_inc(v___x_1961_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1962_, 0, v___x_1961_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1953_);
v___x_1963_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_snd_1949_, v_ident_1950_, v___f_1962_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1951_, v_a_1964_, v___y_1957_);
lean_dec_ref(v___x_1965_);
v___x_1966_ = lean_st_ref_get(v___x_1961_);
lean_dec(v___x_1961_);
v___x_1967_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1966_, v___y_1953_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1953_);
return v___x_1967_;
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v___x_1961_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1953_);
lean_dec(v_fst_1951_);
v_a_1968_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1963_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1963_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed(lean_object* v___x_1976_, lean_object* v_snd_1977_, lean_object* v_ident_1978_, lean_object* v_fst_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(v___x_1976_, v_snd_1977_, v_ident_1978_, v_fst_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(lean_object* v_x_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_1996_);
v___x_2007_ = l_Lean_Syntax_isOfKind(v_x_1996_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_x_1996_);
v___x_2008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = lean_unsigned_to_nat(1u);
v___x_2010_ = l_Lean_Syntax_getArg(v_x_1996_, v___x_2009_);
lean_dec(v_x_1996_);
lean_inc(v___x_2010_);
v___x_2011_ = l_Lean_Syntax_matchesNull(v___x_2010_, v___x_2009_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec(v___x_2010_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v___x_2012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = l_Lean_Syntax_getArg(v___x_2010_, v___x_2013_);
lean_dec(v___x_2010_);
v___x_2015_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_2014_);
v___x_2016_ = l_Lean_Syntax_isOfKind(v___x_2014_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1));
lean_inc(v___x_2014_);
v___x_2018_ = l_Lean_Syntax_isOfKind(v___x_2014_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_dec(v___x_2014_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v___x_2019_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2019_;
}
else
{
lean_object* v_ident_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_ident_2020_ = l_Lean_Syntax_getArg(v___x_2014_, v___x_2009_);
lean_dec(v___x_2014_);
v___x_2021_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
lean_inc(v_ident_2020_);
v___x_2022_ = l_Lean_Syntax_isOfKind(v_ident_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec(v_ident_2020_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v___x_2023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; 
lean_inc(v_a_2004_);
lean_inc_ref(v_a_2003_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
v___x_2024_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1998_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v___x_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v_fst_2026_ = lean_ctor_get(v_a_2025_, 0);
lean_inc(v_fst_2026_);
v_snd_2027_ = lean_ctor_get(v_a_2025_, 1);
lean_inc(v_snd_2027_);
lean_dec(v_a_2025_);
v___x_2028_ = lean_box(0);
lean_inc(v_fst_2026_);
v___f_2029_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2029_, 0, v___x_2028_);
lean_closure_set(v___f_2029_, 1, v_snd_2027_);
lean_closure_set(v___f_2029_, 2, v_ident_2020_);
lean_closure_set(v___f_2029_, 3, v_fst_2026_);
v___x_2030_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2026_, v___f_2029_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2030_;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_ident_2020_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v_a_2031_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2024_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2024_);
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
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2039_ = l_Lean_Syntax_getArg(v___x_2014_, v___x_2013_);
lean_dec(v___x_2014_);
v___x_2040_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_2039_);
v___x_2041_ = l_Lean_Syntax_isOfKind(v___x_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec(v___x_2039_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v___x_2042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2042_;
}
else
{
lean_object* v_ident_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_ident_2043_ = l_Lean_Syntax_getArg(v___x_2039_, v___x_2013_);
lean_dec(v___x_2039_);
v___x_2044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26));
lean_inc(v_ident_2043_);
v___x_2045_ = l_Lean_Syntax_isOfKind(v_ident_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v_ident_2043_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v___x_2046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; 
lean_inc(v_a_2004_);
lean_inc_ref(v_a_2003_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
v___x_2047_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1998_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2051_; lean_object* v___f_2052_; lean_object* v___x_2053_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v_fst_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_fst_2049_);
v_snd_2050_ = lean_ctor_get(v_a_2048_, 1);
lean_inc(v_snd_2050_);
lean_dec(v_a_2048_);
v___x_2051_ = lean_box(0);
lean_inc(v_fst_2049_);
v___f_2052_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2052_, 0, v___x_2051_);
lean_closure_set(v___f_2052_, 1, v_snd_2050_);
lean_closure_set(v___f_2052_, 2, v_ident_2043_);
lean_closure_set(v___f_2052_, 3, v_fst_2049_);
v___x_2053_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2049_, v___f_2052_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2053_;
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_ident_2043_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
v_a_2054_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2047_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2047_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(lean_object* v_x_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(v_x_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(lean_object* v_mvarId_2073_, lean_object* v_val_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_2073_, v_val_2074_, v___y_2080_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(lean_object* v_mvarId_2085_, lean_object* v_val_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(v_mvarId_2085_, v_val_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_object* v_00_u03b1_2097_, lean_object* v_name_2098_, lean_object* v_type_2099_, lean_object* v_val_2100_, lean_object* v_k_2101_, uint8_t v_nondep_2102_, uint8_t v_kind_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_2098_, v_type_2099_, v_val_2100_, v_k_2101_, v_nondep_2102_, v_kind_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_name_2115_, lean_object* v_type_2116_, lean_object* v_val_2117_, lean_object* v_k_2118_, lean_object* v_nondep_2119_, lean_object* v_kind_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_nondep_boxed_2130_; uint8_t v_kind_boxed_2131_; lean_object* v_res_2132_; 
v_nondep_boxed_2130_ = lean_unbox(v_nondep_2119_);
v_kind_boxed_2131_ = lean_unbox(v_kind_2120_);
v_res_2132_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(v_00_u03b1_2114_, v_name_2115_, v_type_2116_, v_val_2117_, v_k_2118_, v_nondep_boxed_2130_, v_kind_boxed_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_object* v_00_u03b1_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(v_00_u03b1_2153_, v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2161_, lean_object* v_name_2162_, uint8_t v_bi_2163_, lean_object* v_type_2164_, lean_object* v_k_2165_, uint8_t v_kind_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_2162_, v_bi_2163_, v_type_2164_, v_k_2165_, v_kind_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_name_2174_, lean_object* v_bi_2175_, lean_object* v_type_2176_, lean_object* v_k_2177_, lean_object* v_kind_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v_bi_boxed_2184_; uint8_t v_kind_boxed_2185_; lean_object* v_res_2186_; 
v_bi_boxed_2184_ = lean_unbox(v_bi_2175_);
v_kind_boxed_2185_ = lean_unbox(v_kind_2178_);
v_res_2186_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(v_00_u03b1_2173_, v_name_2174_, v_bi_boxed_2184_, v_type_2176_, v_k_2177_, v_kind_boxed_2185_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_object* v_00_u03b1_2187_, lean_object* v_name_2188_, lean_object* v_type_2189_, lean_object* v_k_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_2188_, v_type_2189_, v_k_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_name_2198_, lean_object* v_type_2199_, lean_object* v_k_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(v_00_u03b1_2197_, v_name_2198_, v_type_2199_, v_k_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(lean_object* v_00_u03b2_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_x_2208_, v_x_2209_, v_x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2212_, lean_object* v_x_2213_, size_t v_x_2214_, size_t v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_2213_, v_x_2214_, v_x_2215_, v_x_2216_, v_x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
size_t v_x_21791__boxed_2225_; size_t v_x_21792__boxed_2226_; lean_object* v_res_2227_; 
v_x_21791__boxed_2225_ = lean_unbox_usize(v_x_2221_);
lean_dec(v_x_2221_);
v_x_21792__boxed_2226_ = lean_unbox_usize(v_x_2222_);
lean_dec(v_x_2222_);
v_res_2227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(v_00_u03b2_2219_, v_x_2220_, v_x_21791__boxed_2225_, v_x_21792__boxed_2226_, v_x_2223_, v_x_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2228_, lean_object* v_n_2229_, lean_object* v_k_2230_, lean_object* v_v_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v_n_2229_, v_k_2230_, v_v_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b2_2233_, size_t v_depth_2234_, lean_object* v_keys_2235_, lean_object* v_vals_2236_, lean_object* v_heq_2237_, lean_object* v_i_2238_, lean_object* v_entries_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_2234_, v_keys_2235_, v_vals_2236_, v_i_2238_, v_entries_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_depth_2242_, lean_object* v_keys_2243_, lean_object* v_vals_2244_, lean_object* v_heq_2245_, lean_object* v_i_2246_, lean_object* v_entries_2247_){
_start:
{
size_t v_depth_boxed_2248_; lean_object* v_res_2249_; 
v_depth_boxed_2248_ = lean_unbox_usize(v_depth_2242_);
lean_dec(v_depth_2242_);
v_res_2249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(v_00_u03b2_2241_, v_depth_boxed_2248_, v_keys_2243_, v_vals_2244_, v_heq_2245_, v_i_2246_, v_entries_2247_);
lean_dec_ref(v_vals_2244_);
lean_dec_ref(v_keys_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_x_2251_, v_x_2252_, v_x_2253_, v_x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1(){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2267_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2268_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_2269_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3));
v___x_2270_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed), 10, 0);
v___x_2271_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2267_, v___x_2268_, v___x_2269_, v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
return v_res_2273_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
}
#ifdef __cplusplus
}
#endif
