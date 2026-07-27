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
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imp"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(254, 180, 127, 119, 35, 232, 80, 131)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Target not an implication or let-binding "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "entails_cons_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 222, 62, 246, 205, 225, 8, 203)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mintroPat_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 197, 23, 48, 210, 183, 157, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 196, 52, 121, 17, 165, 127, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0;
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMIntro"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 115, 63, 215, 129, 231, 252, 53)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object*);
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
uint8_t v___x_1357__boxed_52_; lean_object* v_res_53_; 
v___x_1357__boxed_52_ = lean_unbox(v___x_50_);
v_res_53_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(v_inst_45_, v_inst_46_, v_type_47_, v_value_48_, v___f_49_, v___x_1357__boxed_52_, v_name_51_);
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
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
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
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
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
lean_inc_n(v_u_110_, 2);
v___x_123_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_110_, v_00_u03c3s_111_, v_hyps_112_, v_H_122_);
v_fst_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc_n(v_fst_124_, 2);
v_snd_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_snd_125_);
lean_dec_ref(v___x_123_);
lean_inc_ref(v___x_117_);
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
uint8_t v___x_1488__boxed_170_; lean_object* v_res_171_; 
v___x_1488__boxed_170_ = lean_unbox(v___x_167_);
v_res_171_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(v_fst_153_, v___x_154_, v_u_155_, v_00_u03c3s_156_, v_hyps_157_, v___x_158_, v___x_159_, v___x_160_, v___x_161_, v___x_162_, v_toPure_163_, v_k_164_, v_toBind_165_, v_snd_166_, v___x_1488__boxed_170_, v_inst_168_, v_uniq_169_);
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
uint8_t v___x_1526__boxed_213_; lean_object* v_res_214_; 
v___x_1526__boxed_213_ = lean_unbox(v___x_208_);
v_res_214_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(v___x_196_, v_u_197_, v_00_u03c3s_198_, v_hyps_199_, v___x_200_, v___x_201_, v___x_202_, v___x_203_, v___x_204_, v_toPure_205_, v_k_206_, v_toBind_207_, v___x_1526__boxed_213_, v_inst_209_, v___x_210_, v___x_211_, v_____x_212_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_instMonadEIO(lean_box(0));
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0);
v___x_217_ = l_StateRefT_x27_instMonad___redArg(v___x_216_);
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
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5));
v___x_248_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17));
v___x_249_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_248_, v___x_247_, v___x_246_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19(void){
_start:
{
lean_object* v___x_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___x_253_; 
v___x_250_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18);
v___f_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4));
v___f_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16));
v___x_253_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_252_, v___f_251_, v___x_250_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_goal_277_, lean_object* v_ident_278_, lean_object* v_k_279_){
_start:
{
lean_object* v___x_280_; lean_object* v_toApplicative_281_; lean_object* v_toFunctor_282_; lean_object* v_toSeq_283_; lean_object* v_toSeqLeft_284_; lean_object* v_toSeqRight_285_; lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___f_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_toApplicative_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_392_; 
v___x_280_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_281_ = lean_ctor_get(v___x_280_, 0);
v_toFunctor_282_ = lean_ctor_get(v_toApplicative_281_, 0);
v_toSeq_283_ = lean_ctor_get(v_toApplicative_281_, 2);
v_toSeqLeft_284_ = lean_ctor_get(v_toApplicative_281_, 3);
v_toSeqRight_285_ = lean_ctor_get(v_toApplicative_281_, 4);
v___f_286_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_282_, 2);
v___f_288_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_288_, 0, v_toFunctor_282_);
v___f_289_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_289_, 0, v_toFunctor_282_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___f_288_);
lean_ctor_set(v___x_290_, 1, v___f_289_);
lean_inc(v_toSeqRight_285_);
v___f_291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_291_, 0, v_toSeqRight_285_);
lean_inc(v_toSeqLeft_284_);
v___f_292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_292_, 0, v_toSeqLeft_284_);
lean_inc(v_toSeq_283_);
v___f_293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_293_, 0, v_toSeq_283_);
v___x_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_294_, 0, v___x_290_);
lean_ctor_set(v___x_294_, 1, v___f_286_);
lean_ctor_set(v___x_294_, 2, v___f_293_);
lean_ctor_set(v___x_294_, 3, v___f_292_);
lean_ctor_set(v___x_294_, 4, v___f_291_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___f_287_);
v___x_296_ = l_StateRefT_x27_instMonad___redArg(v___x_295_);
v_toApplicative_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_296_, 1);
lean_dec(v_unused_393_);
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_392_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_toApplicative_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_392_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_toFunctor_301_; lean_object* v_toSeq_302_; lean_object* v_toSeqLeft_303_; lean_object* v_toSeqRight_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_390_; 
v_toFunctor_301_ = lean_ctor_get(v_toApplicative_297_, 0);
v_toSeq_302_ = lean_ctor_get(v_toApplicative_297_, 2);
v_toSeqLeft_303_ = lean_ctor_get(v_toApplicative_297_, 3);
v_toSeqRight_304_ = lean_ctor_get(v_toApplicative_297_, 4);
v_isSharedCheck_390_ = !lean_is_exclusive(v_toApplicative_297_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_toApplicative_297_, 1);
lean_dec(v_unused_391_);
v___x_306_ = v_toApplicative_297_;
v_isShared_307_ = v_isSharedCheck_390_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_toSeqRight_304_);
lean_inc(v_toSeqLeft_303_);
lean_inc(v_toSeq_302_);
lean_inc(v_toFunctor_301_);
lean_dec(v_toApplicative_297_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_390_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v___f_310_; lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_317_; 
v___f_308_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_309_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_301_);
v___f_310_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_310_, 0, v_toFunctor_301_);
v___f_311_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_311_, 0, v_toFunctor_301_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___f_310_);
lean_ctor_set(v___x_312_, 1, v___f_311_);
v___f_313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_313_, 0, v_toSeqRight_304_);
v___f_314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_314_, 0, v_toSeqLeft_303_);
v___f_315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_315_, 0, v_toSeq_302_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 4, v___f_313_);
lean_ctor_set(v___x_306_, 3, v___f_314_);
lean_ctor_set(v___x_306_, 2, v___f_315_);
lean_ctor_set(v___x_306_, 1, v___f_308_);
lean_ctor_set(v___x_306_, 0, v___x_312_);
v___x_317_ = v___x_306_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___f_308_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___f_315_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v___f_314_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v___f_313_);
v___x_317_ = v_reuseFailAlloc_389_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___f_309_);
lean_ctor_set(v___x_299_, 0, v___x_317_);
v___x_319_ = v___x_299_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___f_309_);
v___x_319_ = v_reuseFailAlloc_388_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_toMonadRef_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_toPure_329_; lean_object* v_u_330_; lean_object* v_00_u03c3s_331_; lean_object* v_hyps_332_; lean_object* v_target_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_320_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9);
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_322_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19);
v_toMonadRef_323_ = lean_ctor_get(v___x_322_, 0);
v___x_324_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_319_);
v___x_325_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_324_, v___x_319_);
lean_inc_ref(v_toMonadRef_323_);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_321_);
lean_ctor_set(v___x_326_, 1, v_toMonadRef_323_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
v_toApplicative_327_ = lean_ctor_get(v_inst_274_, 0);
v_toBind_328_ = lean_ctor_get(v_inst_274_, 1);
v_toPure_329_ = lean_ctor_get(v_toApplicative_327_, 1);
v_u_330_ = lean_ctor_get(v_goal_277_, 0);
lean_inc(v_u_330_);
v_00_u03c3s_331_ = lean_ctor_get(v_goal_277_, 1);
lean_inc_ref(v_00_u03c3s_331_);
v_hyps_332_ = lean_ctor_get(v_goal_277_, 2);
lean_inc_ref(v_hyps_332_);
v_target_333_ = lean_ctor_get(v_goal_277_, 3);
lean_inc_ref(v_target_333_);
lean_dec_ref(v_goal_277_);
v___x_334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20));
v___x_335_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21));
v___x_336_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22));
v___x_337_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_338_ = lean_unsigned_to_nat(3u);
v___x_339_ = l_Lean_Expr_isAppOfArity(v_target_333_, v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
if (lean_obj_tag(v_target_333_) == 8)
{
lean_object* v_declName_340_; lean_object* v_type_341_; lean_object* v_value_342_; lean_object* v_body_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
lean_inc(v_toPure_329_);
lean_inc_n(v_toBind_328_, 2);
lean_dec_ref_known(v___x_326_, 3);
lean_dec_ref(v___x_319_);
v_declName_340_ = lean_ctor_get(v_target_333_, 0);
lean_inc(v_declName_340_);
v_type_341_ = lean_ctor_get(v_target_333_, 1);
lean_inc_ref(v_type_341_);
v_value_342_ = lean_ctor_get(v_target_333_, 2);
lean_inc_ref(v_value_342_);
v_body_343_ = lean_ctor_get(v_target_333_, 3);
lean_inc_ref(v_body_343_);
lean_dec_ref_known(v_target_333_, 4);
lean_inc(v_inst_276_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_344_, 0, v_inst_276_);
lean_closure_set(v___f_344_, 1, v_body_343_);
lean_closure_set(v___f_344_, 2, v_u_330_);
lean_closure_set(v___f_344_, 3, v_00_u03c3s_331_);
lean_closure_set(v___f_344_, 4, v_hyps_332_);
lean_closure_set(v___f_344_, 5, v_k_279_);
lean_closure_set(v___f_344_, 6, v_toBind_328_);
v___x_345_ = lean_box(v___x_339_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_346_, 0, v_inst_275_);
lean_closure_set(v___f_346_, 1, v_inst_274_);
lean_closure_set(v___f_346_, 2, v_type_341_);
lean_closure_set(v___f_346_, 3, v_value_342_);
lean_closure_set(v___f_346_, 4, v___f_344_);
lean_closure_set(v___f_346_, 5, v___x_345_);
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_278_);
v___x_348_ = l_Lean_Syntax_isOfKind(v_ident_278_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_toPure_329_);
lean_dec(v_ident_278_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_349_, 0, v___f_346_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_350_, 0, v_declName_340_);
v___x_351_ = lean_apply_2(v_inst_276_, lean_box(0), v___f_350_);
v___x_352_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_351_, v___f_349_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v_name_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v_name_354_ = l_Lean_Syntax_getArg(v_ident_278_, v___x_353_);
lean_dec(v_ident_278_);
v___x_355_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_354_);
v___x_356_ = l_Lean_Syntax_isOfKind(v_name_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___f_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v_name_354_);
lean_dec(v_toPure_329_);
v___f_357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_357_, 0, v___f_346_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_358_, 0, v_declName_340_);
v___x_359_ = lean_apply_2(v_inst_276_, lean_box(0), v___f_358_);
v___x_360_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_359_, v___f_357_);
return v___x_360_;
}
else
{
lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_declName_340_);
lean_dec(v_inst_276_);
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_361_, 0, v___f_346_);
v___x_362_ = l_Lean_TSyntax_getId(v_name_354_);
lean_dec(v_name_354_);
v___x_363_ = lean_apply_2(v_toPure_329_, lean_box(0), v___x_362_);
v___x_364_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_363_, v___f_361_);
return v___x_364_;
}
}
}
else
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_hyps_332_);
lean_dec_ref(v_00_u03c3s_331_);
lean_dec(v_u_330_);
lean_dec(v_k_279_);
lean_dec(v_ident_278_);
lean_dec_ref(v_inst_275_);
v_isSharedCheck_375_ = !lean_is_exclusive(v_inst_274_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_inst_274_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_inst_274_, 0);
lean_dec(v_unused_377_);
v___x_366_ = v_inst_274_;
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
else
{
lean_dec(v_inst_274_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_369_ = l_Lean_MessageData_ofExpr(v_target_333_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 7);
lean_ctor_set(v___x_366_, 1, v___x_369_);
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_374_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_throwError___redArg(v___x_319_, v___x_326_, v___x_371_);
v___x_373_ = lean_apply_2(v_inst_276_, lean_box(0), v___x_372_);
return v___x_373_;
}
}
}
}
else
{
lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_inc(v_toPure_329_);
lean_inc_n(v_toBind_328_, 2);
lean_dec_ref_known(v___x_326_, 3);
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_274_);
v___f_378_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed), 6, 1);
lean_closure_set(v___f_378_, 0, v_ident_278_);
v___x_379_ = l_Lean_Expr_appFn_x21(v_target_333_);
v___x_380_ = l_Lean_Expr_appFn_x21(v___x_379_);
v___x_381_ = l_Lean_Expr_appArg_x21(v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = l_Lean_Expr_appArg_x21(v___x_379_);
lean_dec_ref(v___x_379_);
v___x_383_ = l_Lean_Expr_appArg_x21(v_target_333_);
lean_dec_ref(v_target_333_);
v___x_384_ = lean_box(v___x_339_);
lean_inc(v_inst_276_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_385_, 0, v___x_382_);
lean_closure_set(v___f_385_, 1, v_u_330_);
lean_closure_set(v___f_385_, 2, v_00_u03c3s_331_);
lean_closure_set(v___f_385_, 3, v_hyps_332_);
lean_closure_set(v___f_385_, 4, v___x_334_);
lean_closure_set(v___f_385_, 5, v___x_335_);
lean_closure_set(v___f_385_, 6, v___x_336_);
lean_closure_set(v___f_385_, 7, v___x_381_);
lean_closure_set(v___f_385_, 8, v___x_383_);
lean_closure_set(v___f_385_, 9, v_toPure_329_);
lean_closure_set(v___f_385_, 10, v_k_279_);
lean_closure_set(v___f_385_, 11, v_toBind_328_);
lean_closure_set(v___f_385_, 12, v___x_384_);
lean_closure_set(v___f_385_, 13, v_inst_276_);
lean_closure_set(v___f_385_, 14, v___x_319_);
lean_closure_set(v___f_385_, 15, v___x_320_);
v___x_386_ = lean_apply_2(v_inst_276_, lean_box(0), v___f_378_);
v___x_387_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_386_, v___f_385_);
return v___x_387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro(lean_object* v_m_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_goal_398_, lean_object* v_ident_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(v_inst_395_, v_inst_396_, v_inst_397_, v_goal_398_, v_ident_399_, v_k_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0(lean_object* v_u_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_hyps_411_, lean_object* v_target_412_, lean_object* v_toPure_413_, lean_object* v_prf_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_416_ = lean_box(0);
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v_u_408_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_mkConst(v___x_415_, v___x_417_);
v___x_419_ = l_Lean_mkApp5(v___x_418_, v___x_409_, v___x_410_, v_hyps_411_, v_target_412_, v_prf_414_);
v___x_420_ = lean_apply_2(v_toPure_413_, lean_box(0), v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(lean_object* v___x_421_, uint8_t v___x_422_, uint8_t v___x_423_, lean_object* v_inst_424_, lean_object* v_toBind_425_, lean_object* v___f_426_, lean_object* v_prf_427_){
_start:
{
uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_428_ = 1;
v___x_429_ = lean_box(v___x_422_);
v___x_430_ = lean_box(v___x_423_);
v___x_431_ = lean_box(v___x_422_);
v___x_432_ = lean_box(v___x_423_);
v___x_433_ = lean_box(v___x_428_);
v___x_434_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_434_, 0, v___x_421_);
lean_closure_set(v___x_434_, 1, v_prf_427_);
lean_closure_set(v___x_434_, 2, v___x_429_);
lean_closure_set(v___x_434_, 3, v___x_430_);
lean_closure_set(v___x_434_, 4, v___x_431_);
lean_closure_set(v___x_434_, 5, v___x_432_);
lean_closure_set(v___x_434_, 6, v___x_433_);
v___x_435_ = lean_apply_2(v_inst_424_, lean_box(0), v___x_434_);
v___x_436_ = lean_apply_4(v_toBind_425_, lean_box(0), lean_box(0), v___x_435_, v___f_426_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed(lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_inst_440_, lean_object* v_toBind_441_, lean_object* v___f_442_, lean_object* v_prf_443_){
_start:
{
uint8_t v___x_2265__boxed_444_; uint8_t v___x_2266__boxed_445_; lean_object* v_res_446_; 
v___x_2265__boxed_444_ = lean_unbox(v___x_438_);
v___x_2266__boxed_445_ = lean_unbox(v___x_439_);
v_res_446_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(v___x_437_, v___x_2265__boxed_444_, v___x_2266__boxed_445_, v_inst_440_, v_toBind_441_, v___f_442_, v_prf_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(lean_object* v___x_447_, lean_object* v_ident_448_, uint8_t v___x_449_, lean_object* v_hyps_450_, lean_object* v___x_451_, lean_object* v_inst_452_, lean_object* v_toBind_453_, lean_object* v___f_454_, lean_object* v_target_455_, lean_object* v_u_456_, lean_object* v_k_457_, lean_object* v_map_458_, lean_object* v_s_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_lctx_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_lctx_465_ = lean_ctor_get(v___y_460_, 2);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_447_);
lean_inc_ref(v_s_459_);
lean_inc_ref(v_lctx_465_);
v___x_467_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_448_, v_lctx_465_, v_s_459_, v___x_466_, v___x_449_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref_known(v___x_467_, 1);
lean_inc_ref(v_s_459_);
v___x_468_ = l_Lean_Expr_app___override(v_hyps_450_, v_s_459_);
lean_inc_ref(v___x_451_);
v___x_469_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_451_, v___x_468_);
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_array_push(v___x_471_, v_s_459_);
v___x_473_ = 0;
v___x_474_ = lean_box(v___x_473_);
v___x_475_ = lean_box(v___x_449_);
lean_inc(v_toBind_453_);
lean_inc_ref(v___x_472_);
v___f_476_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_476_, 0, v___x_472_);
lean_closure_set(v___f_476_, 1, v___x_474_);
lean_closure_set(v___f_476_, 2, v___x_475_);
lean_closure_set(v___f_476_, 3, v_inst_452_);
lean_closure_set(v___f_476_, 4, v_toBind_453_);
lean_closure_set(v___f_476_, 5, v___f_454_);
v___x_477_ = l_Lean_Expr_betaRev(v_target_455_, v___x_472_, v___x_473_, v___x_473_);
lean_dec_ref(v___x_472_);
v___x_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_478_, 0, v_u_456_);
lean_ctor_set(v___x_478_, 1, v___x_451_);
lean_ctor_set(v___x_478_, 2, v___x_469_);
lean_ctor_set(v___x_478_, 3, v___x_477_);
v___x_479_ = lean_apply_1(v_k_457_, v___x_478_);
v___x_480_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v___x_479_, v___f_476_);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
v___x_481_ = lean_apply_7(v_map_458_, lean_box(0), v___x_480_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, lean_box(0));
return v___x_481_;
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v_s_459_);
lean_dec_ref(v_map_458_);
lean_dec(v_k_457_);
lean_dec(v_u_456_);
lean_dec_ref(v_target_455_);
lean_dec(v___f_454_);
lean_dec(v_toBind_453_);
lean_dec(v_inst_452_);
lean_dec_ref(v___x_451_);
lean_dec_ref(v_hyps_450_);
v_a_482_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_467_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_467_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_490_ = _args[0];
lean_object* v_ident_491_ = _args[1];
lean_object* v___x_492_ = _args[2];
lean_object* v_hyps_493_ = _args[3];
lean_object* v___x_494_ = _args[4];
lean_object* v_inst_495_ = _args[5];
lean_object* v_toBind_496_ = _args[6];
lean_object* v___f_497_ = _args[7];
lean_object* v_target_498_ = _args[8];
lean_object* v_u_499_ = _args[9];
lean_object* v_k_500_ = _args[10];
lean_object* v_map_501_ = _args[11];
lean_object* v_s_502_ = _args[12];
lean_object* v___y_503_ = _args[13];
lean_object* v___y_504_ = _args[14];
lean_object* v___y_505_ = _args[15];
lean_object* v___y_506_ = _args[16];
lean_object* v___y_507_ = _args[17];
_start:
{
uint8_t v___x_2298__boxed_508_; lean_object* v_res_509_; 
v___x_2298__boxed_508_ = lean_unbox(v___x_492_);
v_res_509_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(v___x_490_, v_ident_491_, v___x_2298__boxed_508_, v_hyps_493_, v___x_494_, v_inst_495_, v_toBind_496_, v___f_497_, v_target_498_, v_u_499_, v_k_500_, v_map_501_, v_s_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(lean_object* v_goal_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v_toPure_524_, lean_object* v_ident_525_, lean_object* v_inst_526_, lean_object* v_toBind_527_, lean_object* v_k_528_, lean_object* v___x_529_, lean_object* v_map_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_u_536_; lean_object* v_00_u03c3s_537_; lean_object* v_hyps_538_; lean_object* v_target_539_; lean_object* v___x_540_; 
v_u_536_ = lean_ctor_get(v_goal_521_, 0);
lean_inc(v_u_536_);
v_00_u03c3s_537_ = lean_ctor_get(v_goal_521_, 1);
lean_inc_ref_n(v_00_u03c3s_537_, 2);
v_hyps_538_ = lean_ctor_get(v_goal_521_, 2);
lean_inc_ref(v_hyps_538_);
v_target_539_ = lean_ctor_get(v_goal_521_, 3);
lean_inc_ref(v_target_539_);
lean_dec_ref(v_goal_521_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_540_ = lean_whnf(v_00_u03c3s_537_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_543_ = lean_unsigned_to_nat(3u);
v___x_544_ = l_Lean_Expr_isAppOfArity(v_a_541_, v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_2189__overap_548_; lean_object* v___x_549_; 
lean_dec(v_a_541_);
lean_dec_ref(v_target_539_);
lean_dec_ref(v_hyps_538_);
lean_dec(v_u_536_);
lean_dec_ref(v_map_530_);
lean_dec_ref(v___x_529_);
lean_dec(v_k_528_);
lean_dec(v_toBind_527_);
lean_dec(v_inst_526_);
lean_dec(v_ident_525_);
lean_dec(v_toPure_524_);
v___x_545_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_546_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_537_);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_2189__overap_548_ = l_Lean_throwError___redArg(v___x_522_, v___x_523_, v___x_547_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_549_ = lean_apply_5(v___x_2189__overap_548_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, lean_box(0));
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
lean_dec_ref(v_00_u03c3s_537_);
lean_dec_ref(v___x_523_);
v___x_550_ = l_Lean_Expr_appFn_x21(v_a_541_);
v___x_551_ = l_Lean_Expr_appArg_x21(v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_Lean_Expr_appArg_x21(v_a_541_);
lean_dec(v_a_541_);
lean_inc_ref(v_target_539_);
lean_inc_ref(v_hyps_538_);
lean_inc_ref_n(v___x_551_, 2);
lean_inc_ref(v___x_552_);
lean_inc(v_u_536_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0), 7, 6);
lean_closure_set(v___f_553_, 0, v_u_536_);
lean_closure_set(v___f_553_, 1, v___x_552_);
lean_closure_set(v___f_553_, 2, v___x_551_);
lean_closure_set(v___f_553_, 3, v_hyps_538_);
lean_closure_set(v___f_553_, 4, v_target_539_);
lean_closure_set(v___f_553_, 5, v_toPure_524_);
v___x_554_ = lean_box(v___x_544_);
lean_inc_n(v_ident_525_, 2);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed), 18, 12);
lean_closure_set(v___f_555_, 0, v___x_551_);
lean_closure_set(v___f_555_, 1, v_ident_525_);
lean_closure_set(v___f_555_, 2, v___x_554_);
lean_closure_set(v___f_555_, 3, v_hyps_538_);
lean_closure_set(v___f_555_, 4, v___x_552_);
lean_closure_set(v___f_555_, 5, v_inst_526_);
lean_closure_set(v___f_555_, 6, v_toBind_527_);
lean_closure_set(v___f_555_, 7, v___f_553_);
lean_closure_set(v___f_555_, 8, v_target_539_);
lean_closure_set(v___f_555_, 9, v_u_536_);
lean_closure_set(v___f_555_, 10, v_k_528_);
lean_closure_set(v___f_555_, 11, v_map_530_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_557_ = l_Lean_Syntax_isOfKind(v_ident_525_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_ident_525_);
v___x_558_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_559_ = l_Lean_Core_mkFreshUserName(v___x_558_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_2204__overap_561_; lean_object* v___x_562_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_2204__overap_561_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_529_, v___x_522_, v_a_560_, v___x_551_, v___f_555_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_562_ = lean_apply_5(v___x_2204__overap_561_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, lean_box(0));
return v___x_562_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v___f_555_);
lean_dec_ref(v___x_551_);
lean_dec_ref(v___x_529_);
lean_dec_ref(v___x_522_);
v_a_563_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_559_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = l_Lean_Syntax_getArg(v_ident_525_, v___x_571_);
lean_dec(v_ident_525_);
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_572_);
v___x_574_ = l_Lean_Syntax_isOfKind(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v___x_572_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_576_ = l_Lean_Core_mkFreshUserName(v___x_575_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_2218__overap_578_; lean_object* v___x_579_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_2218__overap_578_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_529_, v___x_522_, v_a_577_, v___x_551_, v___f_555_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_579_ = lean_apply_5(v___x_2218__overap_578_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, lean_box(0));
return v___x_579_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___f_555_);
lean_dec_ref(v___x_551_);
lean_dec_ref(v___x_529_);
lean_dec_ref(v___x_522_);
v_a_580_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_576_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_576_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_2223__overap_589_; lean_object* v___x_590_; 
v___x_588_ = l_Lean_TSyntax_getId(v___x_572_);
lean_dec(v___x_572_);
v___x_2223__overap_589_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_529_, v___x_522_, v___x_588_, v___x_551_, v___f_555_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_590_ = lean_apply_5(v___x_2223__overap_589_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, lean_box(0));
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v_target_539_);
lean_dec_ref(v_hyps_538_);
lean_dec_ref(v_00_u03c3s_537_);
lean_dec(v_u_536_);
lean_dec_ref(v_map_530_);
lean_dec_ref(v___x_529_);
lean_dec(v_k_528_);
lean_dec(v_toBind_527_);
lean_dec(v_inst_526_);
lean_dec(v_ident_525_);
lean_dec(v_toPure_524_);
lean_dec_ref(v___x_523_);
lean_dec_ref(v___x_522_);
v_a_591_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_540_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_540_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed(lean_object* v_goal_599_, lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v_toPure_602_, lean_object* v_ident_603_, lean_object* v_inst_604_, lean_object* v_toBind_605_, lean_object* v_k_606_, lean_object* v___x_607_, lean_object* v_map_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(v_goal_599_, v___x_600_, v___x_601_, v_toPure_602_, v_ident_603_, v_inst_604_, v_toBind_605_, v_k_606_, v___x_607_, v_map_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_goal_618_, lean_object* v_ident_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; lean_object* v_toApplicative_622_; lean_object* v_toFunctor_623_; lean_object* v_toSeq_624_; lean_object* v_toSeqLeft_625_; lean_object* v_toSeqRight_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___f_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_toApplicative_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_696_; 
v___x_621_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_622_ = lean_ctor_get(v___x_621_, 0);
v_toFunctor_623_ = lean_ctor_get(v_toApplicative_622_, 0);
v_toSeq_624_ = lean_ctor_get(v_toApplicative_622_, 2);
v_toSeqLeft_625_ = lean_ctor_get(v_toApplicative_622_, 3);
v_toSeqRight_626_ = lean_ctor_get(v_toApplicative_622_, 4);
v___f_627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_628_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_623_, 2);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_629_, 0, v_toFunctor_623_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_630_, 0, v_toFunctor_623_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___f_629_);
lean_ctor_set(v___x_631_, 1, v___f_630_);
lean_inc(v_toSeqRight_626_);
v___f_632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_632_, 0, v_toSeqRight_626_);
lean_inc(v_toSeqLeft_625_);
v___f_633_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_633_, 0, v_toSeqLeft_625_);
lean_inc(v_toSeq_624_);
v___f_634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_634_, 0, v_toSeq_624_);
v___x_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_635_, 0, v___x_631_);
lean_ctor_set(v___x_635_, 1, v___f_627_);
lean_ctor_set(v___x_635_, 2, v___f_634_);
lean_ctor_set(v___x_635_, 3, v___f_633_);
lean_ctor_set(v___x_635_, 4, v___f_632_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___f_628_);
v___x_637_ = l_StateRefT_x27_instMonad___redArg(v___x_636_);
v_toApplicative_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v___x_637_, 1);
lean_dec(v_unused_697_);
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_696_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_toApplicative_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_696_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_toFunctor_642_; lean_object* v_toSeq_643_; lean_object* v_toSeqLeft_644_; lean_object* v_toSeqRight_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_694_; 
v_toFunctor_642_ = lean_ctor_get(v_toApplicative_638_, 0);
v_toSeq_643_ = lean_ctor_get(v_toApplicative_638_, 2);
v_toSeqLeft_644_ = lean_ctor_get(v_toApplicative_638_, 3);
v_toSeqRight_645_ = lean_ctor_get(v_toApplicative_638_, 4);
v_isSharedCheck_694_ = !lean_is_exclusive(v_toApplicative_638_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_toApplicative_638_, 1);
lean_dec(v_unused_695_);
v___x_647_ = v_toApplicative_638_;
v_isShared_648_ = v_isSharedCheck_694_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_toSeqRight_645_);
lean_inc(v_toSeqLeft_644_);
lean_inc(v_toSeq_643_);
lean_inc(v_toFunctor_642_);
lean_dec(v_toApplicative_638_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_694_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_658_; 
v___f_649_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_650_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_642_);
v___f_651_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_651_, 0, v_toFunctor_642_);
v___f_652_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_652_, 0, v_toFunctor_642_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___f_651_);
lean_ctor_set(v___x_653_, 1, v___f_652_);
v___f_654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_654_, 0, v_toSeqRight_645_);
v___f_655_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_655_, 0, v_toSeqLeft_644_);
v___f_656_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_656_, 0, v_toSeq_643_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v___f_654_);
lean_ctor_set(v___x_647_, 3, v___f_655_);
lean_ctor_set(v___x_647_, 2, v___f_656_);
lean_ctor_set(v___x_647_, 1, v___f_649_);
lean_ctor_set(v___x_647_, 0, v___x_653_);
v___x_658_ = v___x_647_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___f_649_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v___f_656_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v___f_655_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v___f_654_);
v___x_658_ = v_reuseFailAlloc_693_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___f_650_);
lean_ctor_set(v___x_640_, 0, v___x_658_);
v___x_660_ = v___x_640_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___f_650_);
v___x_660_ = v_reuseFailAlloc_692_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v_toApplicative_661_; lean_object* v_toFunctor_662_; lean_object* v_toSeq_663_; lean_object* v_toSeqLeft_664_; lean_object* v_toSeqRight_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___x_668_; lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_toMonadRef_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_toApplicative_683_; lean_object* v_toBind_684_; lean_object* v_toPure_685_; lean_object* v_liftWith_686_; lean_object* v_restoreM_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_toApplicative_661_ = lean_ctor_get(v___x_621_, 0);
v_toFunctor_662_ = lean_ctor_get(v_toApplicative_661_, 0);
v_toSeq_663_ = lean_ctor_get(v_toApplicative_661_, 2);
v_toSeqLeft_664_ = lean_ctor_get(v_toApplicative_661_, 3);
v_toSeqRight_665_ = lean_ctor_get(v_toApplicative_661_, 4);
lean_inc_ref_n(v_toFunctor_662_, 2);
v___f_666_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_666_, 0, v_toFunctor_662_);
v___f_667_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_667_, 0, v_toFunctor_662_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___f_666_);
lean_ctor_set(v___x_668_, 1, v___f_667_);
lean_inc(v_toSeqRight_665_);
v___f_669_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_669_, 0, v_toSeqRight_665_);
lean_inc(v_toSeqLeft_664_);
v___f_670_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_670_, 0, v_toSeqLeft_664_);
lean_inc(v_toSeq_663_);
v___f_671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_671_, 0, v_toSeq_663_);
v___x_672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_672_, 0, v___x_668_);
lean_ctor_set(v___x_672_, 1, v___f_627_);
lean_ctor_set(v___x_672_, 2, v___f_671_);
lean_ctor_set(v___x_672_, 3, v___f_670_);
lean_ctor_set(v___x_672_, 4, v___f_669_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___f_628_);
v___x_674_ = l_StateRefT_x27_instMonad___redArg(v___x_673_);
v___x_675_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_675_, 0, lean_box(0));
lean_closure_set(v___x_675_, 1, lean_box(0));
lean_closure_set(v___x_675_, 2, v___x_674_);
v___x_676_ = l_instMonadControlTOfPure___redArg(v___x_675_);
v___x_677_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_678_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19);
v_toMonadRef_679_ = lean_ctor_get(v___x_678_, 0);
v___x_680_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_660_);
v___x_681_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_680_, v___x_660_);
lean_inc_ref(v_toMonadRef_679_);
v___x_682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_682_, 0, v___x_677_);
lean_ctor_set(v___x_682_, 1, v_toMonadRef_679_);
lean_ctor_set(v___x_682_, 2, v___x_681_);
v_toApplicative_683_ = lean_ctor_get(v_inst_615_, 0);
lean_inc_ref(v_toApplicative_683_);
v_toBind_684_ = lean_ctor_get(v_inst_615_, 1);
lean_inc_n(v_toBind_684_, 2);
lean_dec_ref(v_inst_615_);
v_toPure_685_ = lean_ctor_get(v_toApplicative_683_, 1);
lean_inc(v_toPure_685_);
lean_dec_ref(v_toApplicative_683_);
v_liftWith_686_ = lean_ctor_get(v_inst_616_, 0);
lean_inc(v_liftWith_686_);
v_restoreM_687_ = lean_ctor_get(v_inst_616_, 1);
lean_inc(v_restoreM_687_);
lean_dec_ref(v_inst_616_);
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed), 15, 9);
lean_closure_set(v___f_688_, 0, v_goal_618_);
lean_closure_set(v___f_688_, 1, v___x_660_);
lean_closure_set(v___f_688_, 2, v___x_682_);
lean_closure_set(v___f_688_, 3, v_toPure_685_);
lean_closure_set(v___f_688_, 4, v_ident_619_);
lean_closure_set(v___f_688_, 5, v_inst_617_);
lean_closure_set(v___f_688_, 6, v_toBind_684_);
lean_closure_set(v___f_688_, 7, v_k_620_);
lean_closure_set(v___f_688_, 8, v___x_676_);
v___x_689_ = lean_apply_2(v_liftWith_686_, lean_box(0), v___f_688_);
v___x_690_ = lean_apply_1(v_restoreM_687_, lean_box(0));
v___x_691_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_689_, v___x_690_);
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall(lean_object* v_m_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_goal_702_, lean_object* v_ident_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_699_, v_inst_700_, v_inst_701_, v_goal_702_, v_ident_703_, v_k_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(uint8_t v_isZero_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_ref_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_ref_721_ = lean_ctor_get(v___y_718_, 5);
v___x_722_ = l_Lean_SourceInfo_fromRef(v_ref_721_, v_isZero_715_);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3));
v___x_725_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4));
lean_inc_n(v___x_722_, 2);
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_722_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_Syntax_node1(v___x_722_, v___x_724_, v___x_726_);
v___x_728_ = l_Lean_Syntax_node1(v___x_722_, v___x_723_, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed(lean_object* v_isZero_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v_isZero_boxed_736_; lean_object* v_res_737_; 
v_isZero_boxed_736_ = lean_unbox(v_isZero_730_);
v_res_737_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(v_isZero_boxed_736_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_goal_741_, lean_object* v___f_742_, lean_object* v_____do__lift_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_738_, v_inst_739_, v_inst_740_, v_goal_741_, v_____do__lift_743_, v___f_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed(lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_n_748_, lean_object* v_k_749_, lean_object* v_g_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(v_inst_745_, v_inst_746_, v_inst_747_, v_n_748_, v_k_749_, v_g_750_);
lean_dec(v_n_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_goal_755_, lean_object* v_n_756_, lean_object* v_k_757_){
_start:
{
lean_object* v_toBind_758_; lean_object* v_zero_759_; uint8_t v_isZero_760_; 
v_toBind_758_ = lean_ctor_get(v_inst_752_, 1);
lean_inc(v_toBind_758_);
v_zero_759_ = lean_unsigned_to_nat(0u);
v_isZero_760_ = lean_nat_dec_eq(v_n_756_, v_zero_759_);
if (v_isZero_760_ == 1)
{
lean_object* v___x_761_; 
lean_dec(v_toBind_758_);
lean_dec(v_inst_754_);
lean_dec_ref(v_inst_753_);
lean_dec_ref(v_inst_752_);
v___x_761_ = lean_apply_1(v_k_757_, v_goal_755_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v_one_764_; lean_object* v_n_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_762_ = lean_box(v_isZero_760_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_763_, 0, v___x_762_);
v_one_764_ = lean_unsigned_to_nat(1u);
v_n_765_ = lean_nat_sub(v_n_756_, v_one_764_);
lean_inc_n(v_inst_754_, 2);
lean_inc_ref(v_inst_753_);
lean_inc_ref(v_inst_752_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_766_, 0, v_inst_752_);
lean_closure_set(v___f_766_, 1, v_inst_753_);
lean_closure_set(v___f_766_, 2, v_inst_754_);
lean_closure_set(v___f_766_, 3, v_n_765_);
lean_closure_set(v___f_766_, 4, v_k_757_);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2), 6, 5);
lean_closure_set(v___f_767_, 0, v_inst_752_);
lean_closure_set(v___f_767_, 1, v_inst_753_);
lean_closure_set(v___f_767_, 2, v_inst_754_);
lean_closure_set(v___f_767_, 3, v_goal_755_);
lean_closure_set(v___f_767_, 4, v___f_766_);
v___x_768_ = lean_apply_2(v_inst_754_, lean_box(0), v___f_763_);
v___x_769_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_768_, v___f_767_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_n_773_, lean_object* v_k_774_, lean_object* v_g_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_770_, v_inst_771_, v_inst_772_, v_g_775_, v_n_773_, v_k_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___boxed(lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_goal_780_, lean_object* v_n_781_, lean_object* v_k_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_777_, v_inst_778_, v_inst_779_, v_goal_780_, v_n_781_, v_k_782_);
lean_dec(v_n_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(lean_object* v_m_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_goal_788_, lean_object* v_n_789_, lean_object* v_k_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_785_, v_inst_786_, v_inst_787_, v_goal_788_, v_n_789_, v_k_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___boxed(lean_object* v_m_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_goal_796_, lean_object* v_n_797_, lean_object* v_k_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(v_m_792_, v_inst_793_, v_inst_794_, v_inst_795_, v_goal_796_, v_n_797_, v_k_798_);
lean_dec(v_n_797_);
return v_res_799_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10));
v___x_829_ = l_String_toRawSubstring_x27(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0));
v___x_844_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_840_);
v___x_845_ = l_Lean_Syntax_isOfKind(v_x_840_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_x_840_);
v___x_846_ = lean_box(1);
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_a_842_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = l_Lean_Syntax_getArg(v_x_840_, v___x_849_);
lean_dec(v_x_840_);
v___x_851_ = lean_unsigned_to_nat(2u);
v___x_852_ = l_Lean_Syntax_getNumArgs(v___x_850_);
v___x_853_ = lean_nat_dec_le(v___x_851_, v___x_852_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; 
lean_dec(v___x_852_);
lean_inc(v___x_850_);
v___x_854_ = l_Lean_Syntax_matchesNull(v___x_850_, v___x_849_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v___x_850_);
v___x_855_ = lean_box(1);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_a_842_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = l_Lean_Syntax_getArg(v___x_850_, v___x_848_);
lean_dec(v___x_850_);
v___x_858_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_857_);
v___x_859_ = l_Lean_Syntax_isOfKind(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
lean_dec(v___x_857_);
v___x_860_ = l_Lean_Macro_throwUnsupported___redArg(v_a_842_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = l_Lean_Syntax_getArg(v___x_857_, v___x_848_);
lean_dec(v___x_857_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_861_);
v___x_863_ = l_Lean_Syntax_isOfKind(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v_quotContext_864_; lean_object* v_currMacroScope_865_; lean_object* v_ref_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_quotContext_864_ = lean_ctor_get(v_a_841_, 1);
v_currMacroScope_865_ = lean_ctor_get(v_a_841_, 2);
v_ref_866_ = lean_ctor_get(v_a_841_, 5);
v___x_867_ = l_Lean_SourceInfo_fromRef(v_ref_866_, v___x_863_);
v___x_868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_869_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc_n(v___x_867_, 12);
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_867_);
lean_ctor_set(v___x_870_, 1, v___x_843_);
v___x_871_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_872_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_873_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_874_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_873_, v_currMacroScope_865_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_876_, 0, v___x_867_);
lean_ctor_set(v___x_876_, 1, v___x_872_);
lean_ctor_set(v___x_876_, 2, v___x_874_);
lean_ctor_set(v___x_876_, 3, v___x_875_);
lean_inc_ref(v___x_876_);
v___x_877_ = l_Lean_Syntax_node1(v___x_867_, v___x_871_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node1(v___x_867_, v___x_862_, v___x_877_);
v___x_879_ = l_Lean_Syntax_node1(v___x_867_, v___x_858_, v___x_878_);
v___x_880_ = l_Lean_Syntax_node1(v___x_867_, v___x_869_, v___x_879_);
v___x_881_ = l_Lean_Syntax_node2(v___x_867_, v___x_844_, v___x_870_, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
v___x_883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_867_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_885_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
v___x_886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_867_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_867_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_Syntax_node4(v___x_867_, v___x_885_, v___x_886_, v___x_876_, v___x_888_, v___x_861_);
v___x_890_ = l_Lean_Syntax_node3(v___x_867_, v___x_869_, v___x_881_, v___x_883_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node1(v___x_867_, v___x_868_, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v_a_842_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = l_Lean_Syntax_getArg(v___x_861_, v___x_848_);
v___x_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_895_ = l_Lean_Syntax_isOfKind(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v_quotContext_896_; lean_object* v_currMacroScope_897_; lean_object* v_ref_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_quotContext_896_ = lean_ctor_get(v_a_841_, 1);
v_currMacroScope_897_ = lean_ctor_get(v_a_841_, 2);
v_ref_898_ = lean_ctor_get(v_a_841_, 5);
v___x_899_ = l_Lean_SourceInfo_fromRef(v_ref_898_, v___x_895_);
v___x_900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_901_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc_n(v___x_899_, 12);
v___x_902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_843_);
v___x_903_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
lean_inc(v_currMacroScope_897_);
lean_inc(v_quotContext_896_);
v___x_905_ = l_Lean_addMacroScope(v_quotContext_896_, v___x_904_, v_currMacroScope_897_);
v___x_906_ = lean_box(0);
v___x_907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_907_, 0, v___x_899_);
lean_ctor_set(v___x_907_, 1, v___x_903_);
lean_ctor_set(v___x_907_, 2, v___x_905_);
lean_ctor_set(v___x_907_, 3, v___x_906_);
lean_inc_ref(v___x_907_);
v___x_908_ = l_Lean_Syntax_node1(v___x_899_, v___x_894_, v___x_907_);
v___x_909_ = l_Lean_Syntax_node1(v___x_899_, v___x_862_, v___x_908_);
v___x_910_ = l_Lean_Syntax_node1(v___x_899_, v___x_858_, v___x_909_);
v___x_911_ = l_Lean_Syntax_node1(v___x_899_, v___x_901_, v___x_910_);
v___x_912_ = l_Lean_Syntax_node2(v___x_899_, v___x_844_, v___x_902_, v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_899_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
v___x_917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_899_);
lean_ctor_set(v___x_917_, 1, v___x_915_);
v___x_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_899_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_Syntax_node4(v___x_899_, v___x_916_, v___x_917_, v___x_907_, v___x_919_, v___x_861_);
v___x_921_ = l_Lean_Syntax_node3(v___x_899_, v___x_901_, v___x_912_, v___x_914_, v___x_920_);
v___x_922_ = l_Lean_Syntax_node1(v___x_899_, v___x_900_, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_a_842_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_861_);
v___x_924_ = l_Lean_Macro_throwUnsupported___redArg(v_a_842_);
return v___x_924_;
}
}
}
}
}
else
{
lean_object* v_ref_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_pats_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_ref_925_ = lean_ctor_get(v_a_841_, 5);
v___x_926_ = l_Lean_Syntax_getArg(v___x_850_, v___x_848_);
v___x_927_ = l_Lean_Syntax_getArg(v___x_850_, v___x_849_);
v___x_928_ = l_Lean_Syntax_getArgs(v___x_850_);
lean_dec(v___x_850_);
v___x_929_ = l_Array_extract___redArg(v___x_928_, v___x_851_, v___x_852_);
lean_dec_ref(v___x_928_);
v___x_930_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
v___x_931_ = lean_box(2);
v___x_932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
lean_ctor_set(v___x_932_, 2, v___x_929_);
v_pats_933_ = l_Lean_Syntax_getArgs(v___x_932_);
lean_dec_ref_known(v___x_932_, 3);
v___x_934_ = 0;
v___x_935_ = l_Lean_SourceInfo_fromRef(v_ref_925_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
lean_inc_n(v___x_935_, 7);
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_843_);
v___x_938_ = l_Lean_Syntax_node1(v___x_935_, v___x_930_, v___x_926_);
lean_inc_ref(v___x_937_);
v___x_939_ = l_Lean_Syntax_node2(v___x_935_, v___x_844_, v___x_937_, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_935_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Array_mkArray1___redArg(v___x_927_);
v___x_943_ = l_Array_append___redArg(v___x_942_, v_pats_933_);
lean_dec_ref(v_pats_933_);
v___x_944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_944_, 0, v___x_935_);
lean_ctor_set(v___x_944_, 1, v___x_930_);
lean_ctor_set(v___x_944_, 2, v___x_943_);
v___x_945_ = l_Lean_Syntax_node2(v___x_935_, v___x_844_, v___x_937_, v___x_944_);
v___x_946_ = l_Lean_Syntax_node3(v___x_935_, v___x_930_, v___x_939_, v___x_941_, v___x_945_);
v___x_947_ = l_Lean_Syntax_node1(v___x_935_, v___x_936_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_a_842_);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object* v_x_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(v_x_949_, v_a_950_, v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_952_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___boxed(lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(lean_object* v_00_u03b1_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___boxed(lean_object* v_00_u03b1_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(v_00_u03b1_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
v___x_993_ = lean_apply_9(v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed(lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(lean_object* v_mvarId_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___f_1016_; lean_object* v___x_1017_; 
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1016_, 0, v_x_1006_);
lean_closure_set(v___f_1016_, 1, v___y_1007_);
lean_closure_set(v___f_1016_, 2, v___y_1008_);
lean_closure_set(v___f_1016_, 3, v___y_1009_);
lean_closure_set(v___f_1016_, 4, v___y_1010_);
v___x_1017_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1005_, v___f_1016_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1017_) == 0)
{
return v___x_1017_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___boxed(lean_object* v_mvarId_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1026_, v_x_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(lean_object* v_00_u03b1_1038_, lean_object* v_mvarId_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1039_, v_x_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_mvarId_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(v_00_u03b1_1051_, v_mvarId_1052_, v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(lean_object* v_val_1064_, lean_object* v_newGoal_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1065_);
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1075_, v___x_1076_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1089_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1089_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1089_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1082_ = lean_st_ref_take(v_val_1064_);
v___x_1083_ = l_Lean_Expr_mvarId_x21(v_a_1078_);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
v___x_1085_ = lean_st_ref_set(v_val_1064_, v___x_1084_);
if (v_isShared_1081_ == 0)
{
v___x_1087_ = v___x_1080_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1078_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed(lean_object* v_val_1090_, lean_object* v_newGoal_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(v_val_1090_, v_newGoal_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_val_1090_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_ks_1106_; lean_object* v_vs_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1131_; 
v_ks_1106_ = lean_ctor_get(v_x_1102_, 0);
v_vs_1107_ = lean_ctor_get(v_x_1102_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1109_ = v_x_1102_;
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_vs_1107_);
lean_inc(v_ks_1106_);
lean_dec(v_x_1102_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_array_get_size(v_ks_1106_);
v___x_1112_ = lean_nat_dec_lt(v_x_1103_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_dec(v_x_1103_);
v___x_1113_ = lean_array_push(v_ks_1106_, v_x_1104_);
v___x_1114_ = lean_array_push(v_vs_1107_, v_x_1105_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1114_);
lean_ctor_set(v___x_1109_, 0, v___x_1113_);
v___x_1116_ = v___x_1109_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
lean_object* v_k_x27_1118_; uint8_t v___x_1119_; 
v_k_x27_1118_ = lean_array_fget_borrowed(v_ks_1106_, v_x_1103_);
v___x_1119_ = l_Lean_instBEqMVarId_beq(v_x_1104_, v_k_x27_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1121_; 
if (v_isShared_1110_ == 0)
{
v___x_1121_ = v___x_1109_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_ks_1106_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_vs_1107_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_x_1103_, v___x_1122_);
lean_dec(v_x_1103_);
v_x_1102_ = v___x_1121_;
v_x_1103_ = v___x_1123_;
goto _start;
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1126_ = lean_array_fset(v_ks_1106_, v_x_1103_, v_x_1104_);
v___x_1127_ = lean_array_fset(v_vs_1107_, v_x_1103_, v_x_1105_);
lean_dec(v_x_1103_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1127_);
lean_ctor_set(v___x_1109_, 0, v___x_1126_);
v___x_1129_ = v___x_1109_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_n_1132_, lean_object* v_k_1133_, lean_object* v_v_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_n_1132_, v___x_1135_, v_k_1133_, v_v_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(lean_object* v_x_1138_, size_t v_x_1139_, size_t v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
lean_object* v_es_1143_; size_t v___x_1144_; size_t v___x_1145_; lean_object* v_j_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_es_1143_ = lean_ctor_get(v_x_1138_, 0);
v___x_1144_ = ((size_t)31ULL);
v___x_1145_ = lean_usize_land(v_x_1139_, v___x_1144_);
v_j_1146_ = lean_usize_to_nat(v___x_1145_);
v___x_1147_ = lean_array_get_size(v_es_1143_);
v___x_1148_ = lean_nat_dec_lt(v_j_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec(v_j_1146_);
lean_dec(v_x_1142_);
lean_dec(v_x_1141_);
return v_x_1138_;
}
else
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1187_; 
lean_inc_ref(v_es_1143_);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_x_1138_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_x_1138_, 0);
lean_dec(v_unused_1188_);
v___x_1150_ = v_x_1138_;
v_isShared_1151_ = v_isSharedCheck_1187_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v_x_1138_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1187_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_v_1152_; lean_object* v___x_1153_; lean_object* v_xs_x27_1154_; lean_object* v___y_1156_; 
v_v_1152_ = lean_array_fget(v_es_1143_, v_j_1146_);
v___x_1153_ = lean_box(0);
v_xs_x27_1154_ = lean_array_fset(v_es_1143_, v_j_1146_, v___x_1153_);
switch(lean_obj_tag(v_v_1152_))
{
case 0:
{
lean_object* v_key_1161_; lean_object* v_val_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_key_1161_ = lean_ctor_get(v_v_1152_, 0);
v_val_1162_ = lean_ctor_get(v_v_1152_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_v_1152_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1164_ = v_v_1152_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_val_1162_);
lean_inc(v_key_1161_);
lean_dec(v_v_1152_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
uint8_t v___x_1166_; 
v___x_1166_ = l_Lean_instBEqMVarId_beq(v_x_1141_, v_key_1161_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_del_object(v___x_1164_);
v___x_1167_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1161_, v_val_1162_, v_x_1141_, v_x_1142_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
v___y_1156_ = v___x_1168_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1170_; 
lean_dec(v_val_1162_);
lean_dec(v_key_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v_x_1142_);
lean_ctor_set(v___x_1164_, 0, v_x_1141_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_x_1141_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_x_1142_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
v___y_1156_ = v___x_1170_;
goto v___jp_1155_;
}
}
}
}
case 1:
{
lean_object* v_node_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1185_; 
v_node_1173_ = lean_ctor_get(v_v_1152_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_v_1152_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1175_ = v_v_1152_;
v_isShared_1176_ = v_isSharedCheck_1185_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_node_1173_);
lean_dec(v_v_1152_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1185_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1177_ = ((size_t)5ULL);
v___x_1178_ = lean_usize_shift_right(v_x_1139_, v___x_1177_);
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_add(v_x_1140_, v___x_1179_);
v___x_1181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_node_1173_, v___x_1178_, v___x_1180_, v_x_1141_, v_x_1142_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1181_);
v___x_1183_ = v___x_1175_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
v___y_1156_ = v___x_1183_;
goto v___jp_1155_;
}
}
}
default: 
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_x_1141_);
lean_ctor_set(v___x_1186_, 1, v_x_1142_);
v___y_1156_ = v___x_1186_;
goto v___jp_1155_;
}
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_array_fset(v_xs_x27_1154_, v_j_1146_, v___y_1156_);
lean_dec(v_j_1146_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1157_);
v___x_1159_ = v___x_1150_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
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
else
{
lean_object* v_ks_1189_; lean_object* v_vs_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1210_; 
v_ks_1189_ = lean_ctor_get(v_x_1138_, 0);
v_vs_1190_ = lean_ctor_get(v_x_1138_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1138_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1192_ = v_x_1138_;
v_isShared_1193_ = v_isSharedCheck_1210_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_vs_1190_);
lean_inc(v_ks_1189_);
lean_dec(v_x_1138_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1210_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_ks_1189_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_vs_1190_);
v___x_1195_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v_newNode_1196_; uint8_t v___y_1198_; size_t v___x_1204_; uint8_t v___x_1205_; 
v_newNode_1196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v___x_1195_, v_x_1141_, v_x_1142_);
v___x_1204_ = ((size_t)7ULL);
v___x_1205_ = lean_usize_dec_le(v___x_1204_, v_x_1140_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1206_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1196_);
v___x_1207_ = lean_unsigned_to_nat(4u);
v___x_1208_ = lean_nat_dec_lt(v___x_1206_, v___x_1207_);
lean_dec(v___x_1206_);
v___y_1198_ = v___x_1208_;
goto v___jp_1197_;
}
else
{
v___y_1198_ = v___x_1205_;
goto v___jp_1197_;
}
v___jp_1197_:
{
if (v___y_1198_ == 0)
{
lean_object* v_ks_1199_; lean_object* v_vs_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_ks_1199_ = lean_ctor_get(v_newNode_1196_, 0);
lean_inc_ref(v_ks_1199_);
v_vs_1200_ = lean_ctor_get(v_newNode_1196_, 1);
lean_inc_ref(v_vs_1200_);
lean_dec_ref(v_newNode_1196_);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0);
v___x_1203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_x_1140_, v_ks_1199_, v_vs_1200_, v___x_1201_, v___x_1202_);
lean_dec_ref(v_vs_1200_);
lean_dec_ref(v_ks_1199_);
return v___x_1203_;
}
else
{
return v_newNode_1196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(size_t v_depth_1211_, lean_object* v_keys_1212_, lean_object* v_vals_1213_, lean_object* v_i_1214_, lean_object* v_entries_1215_){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_array_get_size(v_keys_1212_);
v___x_1217_ = lean_nat_dec_lt(v_i_1214_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_i_1214_);
return v_entries_1215_;
}
else
{
lean_object* v_k_1218_; lean_object* v_v_1219_; uint64_t v___x_1220_; size_t v_h_1221_; size_t v___x_1222_; lean_object* v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v_h_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_k_1218_ = lean_array_fget_borrowed(v_keys_1212_, v_i_1214_);
v_v_1219_ = lean_array_fget_borrowed(v_vals_1213_, v_i_1214_);
v___x_1220_ = l_Lean_instHashableMVarId_hash(v_k_1218_);
v_h_1221_ = lean_uint64_to_usize(v___x_1220_);
v___x_1222_ = ((size_t)5ULL);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_sub(v_depth_1211_, v___x_1224_);
v___x_1226_ = lean_usize_mul(v___x_1222_, v___x_1225_);
v_h_1227_ = lean_usize_shift_right(v_h_1221_, v___x_1226_);
v___x_1228_ = lean_nat_add(v_i_1214_, v___x_1223_);
lean_dec(v_i_1214_);
lean_inc(v_v_1219_);
lean_inc(v_k_1218_);
v___x_1229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_entries_1215_, v_h_1227_, v_depth_1211_, v_k_1218_, v_v_1219_);
v_i_1214_ = v___x_1228_;
v_entries_1215_ = v___x_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_depth_1231_, lean_object* v_keys_1232_, lean_object* v_vals_1233_, lean_object* v_i_1234_, lean_object* v_entries_1235_){
_start:
{
size_t v_depth_boxed_1236_; lean_object* v_res_1237_; 
v_depth_boxed_1236_ = lean_unbox_usize(v_depth_1231_);
lean_dec(v_depth_1231_);
v_res_1237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_boxed_1236_, v_keys_1232_, v_vals_1233_, v_i_1234_, v_entries_1235_);
lean_dec_ref(v_vals_1233_);
lean_dec_ref(v_keys_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
size_t v_x_20299__boxed_1243_; size_t v_x_20300__boxed_1244_; lean_object* v_res_1245_; 
v_x_20299__boxed_1243_ = lean_unbox_usize(v_x_1239_);
lean_dec(v_x_1239_);
v_x_20300__boxed_1244_ = lean_unbox_usize(v_x_1240_);
lean_dec(v_x_1240_);
v_res_1245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1238_, v_x_20299__boxed_1243_, v_x_20300__boxed_1244_, v_x_1241_, v_x_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint64_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = l_Lean_instHashableMVarId_hash(v_x_1247_);
v___x_1250_ = lean_uint64_to_usize(v___x_1249_);
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1246_, v___x_1250_, v___x_1251_, v_x_1247_, v_x_1248_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(lean_object* v_mvarId_1253_, lean_object* v_val_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_mctx_1258_; lean_object* v_cache_1259_; lean_object* v_zetaDeltaFVarIds_1260_; lean_object* v_postponed_1261_; lean_object* v_diag_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1290_; 
v___x_1257_ = lean_st_ref_take(v___y_1255_);
v_mctx_1258_ = lean_ctor_get(v___x_1257_, 0);
v_cache_1259_ = lean_ctor_get(v___x_1257_, 1);
v_zetaDeltaFVarIds_1260_ = lean_ctor_get(v___x_1257_, 2);
v_postponed_1261_ = lean_ctor_get(v___x_1257_, 3);
v_diag_1262_ = lean_ctor_get(v___x_1257_, 4);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1264_ = v___x_1257_;
v_isShared_1265_ = v_isSharedCheck_1290_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_diag_1262_);
lean_inc(v_postponed_1261_);
lean_inc(v_zetaDeltaFVarIds_1260_);
lean_inc(v_cache_1259_);
lean_inc(v_mctx_1258_);
lean_dec(v___x_1257_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1290_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_depth_1266_; lean_object* v_levelAssignDepth_1267_; lean_object* v_lmvarCounter_1268_; lean_object* v_mvarCounter_1269_; lean_object* v_lDecls_1270_; lean_object* v_decls_1271_; lean_object* v_userNames_1272_; lean_object* v_lAssignment_1273_; lean_object* v_eAssignment_1274_; lean_object* v_dAssignment_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1289_; 
v_depth_1266_ = lean_ctor_get(v_mctx_1258_, 0);
v_levelAssignDepth_1267_ = lean_ctor_get(v_mctx_1258_, 1);
v_lmvarCounter_1268_ = lean_ctor_get(v_mctx_1258_, 2);
v_mvarCounter_1269_ = lean_ctor_get(v_mctx_1258_, 3);
v_lDecls_1270_ = lean_ctor_get(v_mctx_1258_, 4);
v_decls_1271_ = lean_ctor_get(v_mctx_1258_, 5);
v_userNames_1272_ = lean_ctor_get(v_mctx_1258_, 6);
v_lAssignment_1273_ = lean_ctor_get(v_mctx_1258_, 7);
v_eAssignment_1274_ = lean_ctor_get(v_mctx_1258_, 8);
v_dAssignment_1275_ = lean_ctor_get(v_mctx_1258_, 9);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_mctx_1258_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1277_ = v_mctx_1258_;
v_isShared_1278_ = v_isSharedCheck_1289_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_dAssignment_1275_);
lean_inc(v_eAssignment_1274_);
lean_inc(v_lAssignment_1273_);
lean_inc(v_userNames_1272_);
lean_inc(v_decls_1271_);
lean_inc(v_lDecls_1270_);
lean_inc(v_mvarCounter_1269_);
lean_inc(v_lmvarCounter_1268_);
lean_inc(v_levelAssignDepth_1267_);
lean_inc(v_depth_1266_);
lean_dec(v_mctx_1258_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1289_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_eAssignment_1274_, v_mvarId_1253_, v_val_1254_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 8, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_depth_1266_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_levelAssignDepth_1267_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_lmvarCounter_1268_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_mvarCounter_1269_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_lDecls_1270_);
lean_ctor_set(v_reuseFailAlloc_1288_, 5, v_decls_1271_);
lean_ctor_set(v_reuseFailAlloc_1288_, 6, v_userNames_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 7, v_lAssignment_1273_);
lean_ctor_set(v_reuseFailAlloc_1288_, 8, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1288_, 9, v_dAssignment_1275_);
v___x_1281_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1281_);
v___x_1283_ = v___x_1264_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_cache_1259_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_zetaDeltaFVarIds_1260_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_postponed_1261_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_diag_1262_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_st_ref_set(v___y_1255_, v___x_1283_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(lean_object* v_mvarId_1291_, lean_object* v_val_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_1291_, v_val_1292_, v___y_1293_);
lean_dec(v___y_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_k_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
v___x_1303_ = lean_apply_6(v_k_1296_, v_b_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, lean_box(0));
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_k_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_1304_, v_b_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(lean_object* v_name_1312_, uint8_t v_bi_1313_, lean_object* v_type_1314_, lean_object* v_k_1315_, uint8_t v_kind_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___f_1322_; lean_object* v___x_1323_; 
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1322_, 0, v_k_1315_);
v___x_1323_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1312_, v_bi_1313_, v_type_1314_, v___f_1322_, v_kind_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1323_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1323_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_name_1340_, lean_object* v_bi_1341_, lean_object* v_type_1342_, lean_object* v_k_1343_, lean_object* v_kind_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v_bi_boxed_1350_; uint8_t v_kind_boxed_1351_; lean_object* v_res_1352_; 
v_bi_boxed_1350_ = lean_unbox(v_bi_1341_);
v_kind_boxed_1351_ = lean_unbox(v_kind_1344_);
v_res_1352_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1340_, v_bi_boxed_1350_, v_type_1342_, v_k_1343_, v_kind_boxed_1351_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(lean_object* v_name_1353_, lean_object* v_type_1354_, lean_object* v_k_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = 0;
v___x_1362_ = 0;
v___x_1363_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1353_, v___x_1361_, v_type_1354_, v_k_1355_, v___x_1362_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(lean_object* v_name_1364_, lean_object* v_type_1365_, lean_object* v_k_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_1364_, v_type_1365_, v_k_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(lean_object* v_msgData_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_env_1380_; lean_object* v___x_1381_; lean_object* v_mctx_1382_; lean_object* v_lctx_1383_; lean_object* v_options_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1379_ = lean_st_ref_get(v___y_1377_);
v_env_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_env_1380_);
lean_dec(v___x_1379_);
v___x_1381_ = lean_st_ref_get(v___y_1375_);
v_mctx_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_ref(v_mctx_1382_);
lean_dec(v___x_1381_);
v_lctx_1383_ = lean_ctor_get(v___y_1374_, 2);
v_options_1384_ = lean_ctor_get(v___y_1376_, 2);
lean_inc_ref(v_options_1384_);
lean_inc_ref(v_lctx_1383_);
v___x_1385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1385_, 0, v_env_1380_);
lean_ctor_set(v___x_1385_, 1, v_mctx_1382_);
lean_ctor_set(v___x_1385_, 2, v_lctx_1383_);
lean_ctor_set(v___x_1385_, 3, v_options_1384_);
v___x_1386_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_msgData_1373_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_ref_1401_; lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1411_; 
v_ref_1401_ = lean_ctor_get(v___y_1398_, 5);
v___x_1402_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msg_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_inc(v_ref_1401_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_ref_1401_);
lean_ctor_set(v___x_1407_, 1, v_a_1403_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 1);
lean_ctor_set(v___x_1405_, 0, v___x_1407_);
v___x_1409_ = v___x_1405_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(lean_object* v___x_1419_, lean_object* v_ident_1420_, uint8_t v___x_1421_, lean_object* v_hyps_1422_, lean_object* v___x_1423_, lean_object* v_target_1424_, lean_object* v_u_1425_, lean_object* v_k_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v_s_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_lctx_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_lctx_1437_ = lean_ctor_get(v___y_1432_, 2);
lean_inc_ref(v___x_1419_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1419_);
lean_inc_ref(v_s_1431_);
lean_inc_ref(v_lctx_1437_);
v___x_1439_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_1420_, v_lctx_1437_, v_s_1431_, v___x_1438_, v___x_1421_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref_known(v___x_1439_, 1);
lean_inc_ref(v_s_1431_);
lean_inc_ref(v_hyps_1422_);
v___x_1440_ = l_Lean_Expr_app___override(v_hyps_1422_, v_s_1431_);
lean_inc_ref_n(v___x_1423_, 2);
v___x_1441_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_1423_, v___x_1440_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1444_ = lean_array_push(v___x_1443_, v_s_1431_);
v___x_1445_ = 0;
lean_inc_ref(v_target_1424_);
v___x_1446_ = l_Lean_Expr_betaRev(v_target_1424_, v___x_1444_, v___x_1445_, v___x_1445_);
lean_inc(v_u_1425_);
v___x_1447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1447_, 0, v_u_1425_);
lean_ctor_set(v___x_1447_, 1, v___x_1423_);
lean_ctor_set(v___x_1447_, 2, v___x_1441_);
lean_ctor_set(v___x_1447_, 3, v___x_1446_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
v___x_1448_ = lean_apply_10(v_k_1426_, v___x_1447_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, lean_box(0));
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = 1;
v___x_1451_ = l_Lean_Meta_mkLambdaFVars(v___x_1444_, v_a_1449_, v___x_1445_, v___x_1421_, v___x_1445_, v___x_1421_, v___x_1450_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec_ref(v___x_1444_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1464_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1464_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1464_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_u_1425_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_mkConst(v___x_1456_, v___x_1458_);
v___x_1460_ = l_Lean_mkApp5(v___x_1459_, v___x_1423_, v___x_1419_, v_hyps_1422_, v_target_1424_, v_a_1452_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1460_);
v___x_1462_ = v___x_1454_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_dec(v_u_1425_);
lean_dec_ref(v_target_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v_hyps_1422_);
lean_dec_ref(v___x_1419_);
return v___x_1451_;
}
}
else
{
lean_dec_ref(v___x_1444_);
lean_dec(v_u_1425_);
lean_dec_ref(v_target_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v_hyps_1422_);
lean_dec_ref(v___x_1419_);
return v___x_1448_;
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_s_1431_);
lean_dec_ref(v_k_1426_);
lean_dec(v_u_1425_);
lean_dec_ref(v_target_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v_hyps_1422_);
lean_dec_ref(v___x_1419_);
v_a_1465_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1439_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1439_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_1473_ = _args[0];
lean_object* v_ident_1474_ = _args[1];
lean_object* v___x_1475_ = _args[2];
lean_object* v_hyps_1476_ = _args[3];
lean_object* v___x_1477_ = _args[4];
lean_object* v_target_1478_ = _args[5];
lean_object* v_u_1479_ = _args[6];
lean_object* v_k_1480_ = _args[7];
lean_object* v___y_1481_ = _args[8];
lean_object* v___y_1482_ = _args[9];
lean_object* v___y_1483_ = _args[10];
lean_object* v___y_1484_ = _args[11];
lean_object* v_s_1485_ = _args[12];
lean_object* v___y_1486_ = _args[13];
lean_object* v___y_1487_ = _args[14];
lean_object* v___y_1488_ = _args[15];
lean_object* v___y_1489_ = _args[16];
lean_object* v___y_1490_ = _args[17];
_start:
{
uint8_t v___x_20672__boxed_1491_; lean_object* v_res_1492_; 
v___x_20672__boxed_1491_ = lean_unbox(v___x_1475_);
v_res_1492_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_1473_, v_ident_1474_, v___x_20672__boxed_1491_, v_hyps_1476_, v___x_1477_, v_target_1478_, v_u_1479_, v_k_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v_s_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(lean_object* v_goal_1493_, lean_object* v_ident_1494_, lean_object* v_k_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___y_1506_; lean_object* v_u_1515_; lean_object* v_00_u03c3s_1516_; lean_object* v_hyps_1517_; lean_object* v_target_1518_; lean_object* v___x_1519_; 
v_u_1515_ = lean_ctor_get(v_goal_1493_, 0);
lean_inc(v_u_1515_);
v_00_u03c3s_1516_ = lean_ctor_get(v_goal_1493_, 1);
lean_inc_ref_n(v_00_u03c3s_1516_, 2);
v_hyps_1517_ = lean_ctor_get(v_goal_1493_, 2);
lean_inc_ref(v_hyps_1517_);
v_target_1518_ = lean_ctor_get(v_goal_1493_, 3);
lean_inc_ref(v_target_1518_);
lean_dec_ref(v_goal_1493_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
v___x_1519_ = lean_whnf(v_00_u03c3s_1516_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_1522_ = lean_unsigned_to_nat(3u);
v___x_1523_ = l_Lean_Expr_isAppOfArity(v_a_1520_, v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_target_1518_);
lean_dec_ref(v_hyps_1517_);
lean_dec(v_u_1515_);
lean_dec_ref(v_k_1495_);
lean_dec(v_ident_1494_);
v___x_1524_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_1525_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_1516_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1526_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
v___y_1506_ = v___x_1527_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
lean_dec_ref(v_00_u03c3s_1516_);
v___x_1528_ = l_Lean_Expr_appFn_x21(v_a_1520_);
v___x_1529_ = l_Lean_Expr_appArg_x21(v___x_1528_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = l_Lean_Expr_appArg_x21(v_a_1520_);
lean_dec(v_a_1520_);
v___x_1531_ = lean_box(v___x_1523_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc_n(v_ident_1494_, 2);
lean_inc_ref(v___x_1529_);
v___f_1532_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1532_, 0, v___x_1529_);
lean_closure_set(v___f_1532_, 1, v_ident_1494_);
lean_closure_set(v___f_1532_, 2, v___x_1531_);
lean_closure_set(v___f_1532_, 3, v_hyps_1517_);
lean_closure_set(v___f_1532_, 4, v___x_1530_);
lean_closure_set(v___f_1532_, 5, v_target_1518_);
lean_closure_set(v___f_1532_, 6, v_u_1515_);
lean_closure_set(v___f_1532_, 7, v_k_1495_);
lean_closure_set(v___f_1532_, 8, v___y_1496_);
lean_closure_set(v___f_1532_, 9, v___y_1497_);
lean_closure_set(v___f_1532_, 10, v___y_1498_);
lean_closure_set(v___f_1532_, 11, v___y_1499_);
v___x_1533_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_1534_ = l_Lean_Syntax_isOfKind(v_ident_1494_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_ident_1494_);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1536_ = l_Lean_Core_mkFreshUserName(v___x_1535_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1537_, v___x_1529_, v___f_1532_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
v___y_1506_ = v___x_1538_;
goto v___jp_1505_;
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___f_1532_);
lean_dec_ref(v___x_1529_);
v_a_1539_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1536_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1536_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = l_Lean_Syntax_getArg(v_ident_1494_, v___x_1547_);
lean_dec(v_ident_1494_);
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_1548_);
v___x_1550_ = l_Lean_Syntax_isOfKind(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v___x_1548_);
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1552_ = l_Lean_Core_mkFreshUserName(v___x_1551_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1553_, v___x_1529_, v___f_1532_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
v___y_1506_ = v___x_1554_;
goto v___jp_1505_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v___f_1532_);
lean_dec_ref(v___x_1529_);
v_a_1555_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1552_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1552_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = l_Lean_TSyntax_getId(v___x_1548_);
lean_dec(v___x_1548_);
v___x_1564_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v___x_1563_, v___x_1529_, v___f_1532_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
v___y_1506_ = v___x_1564_;
goto v___jp_1505_;
}
}
}
}
else
{
lean_dec_ref(v_target_1518_);
lean_dec_ref(v_hyps_1517_);
lean_dec_ref(v_00_u03c3s_1516_);
lean_dec(v_u_1515_);
lean_dec_ref(v_k_1495_);
lean_dec(v_ident_1494_);
return v___x_1519_;
}
v___jp_1505_:
{
if (lean_obj_tag(v___y_1506_) == 0)
{
return v___y_1506_;
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_a_1507_ = lean_ctor_get(v___y_1506_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___y_1506_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___y_1506_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___y_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(lean_object* v_goal_1565_, lean_object* v_ident_1566_, lean_object* v_k_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_1565_, v_ident_1566_, v_k_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(lean_object* v___x_1578_, lean_object* v_snd_1579_, lean_object* v_ident_1580_, lean_object* v_fst_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_st_mk_ref(v___x_1578_);
lean_inc(v___x_1591_);
v___f_1592_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1592_, 0, v___x_1591_);
v___x_1593_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_snd_1579_, v_ident_1580_, v___f_1592_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1581_, v_a_1594_, v___y_1587_);
lean_dec_ref(v___x_1595_);
v___x_1596_ = lean_st_ref_get(v___x_1591_);
lean_dec(v___x_1591_);
v___x_1597_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1596_, v___y_1583_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v___x_1597_;
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v___x_1591_);
lean_dec(v_fst_1581_);
v_a_1598_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1593_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1593_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(lean_object* v___x_1606_, lean_object* v_snd_1607_, lean_object* v_ident_1608_, lean_object* v_fst_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(v___x_1606_, v_snd_1607_, v_ident_1608_, v_fst_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(lean_object* v_k_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
v___x_1631_ = lean_apply_10(v_k_1620_, v_b_1625_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, lean_box(0));
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(lean_object* v_k_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v_b_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(lean_object* v_name_1644_, lean_object* v_type_1645_, lean_object* v_val_1646_, lean_object* v_k_1647_, uint8_t v_nondep_1648_, uint8_t v_kind_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___f_1659_; lean_object* v___x_1660_; 
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1659_, 0, v_k_1647_);
lean_closure_set(v___f_1659_, 1, v___y_1650_);
lean_closure_set(v___f_1659_, 2, v___y_1651_);
lean_closure_set(v___f_1659_, 3, v___y_1652_);
lean_closure_set(v___f_1659_, 4, v___y_1653_);
v___x_1660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1644_, v_type_1645_, v_val_1646_, v___f_1659_, v_nondep_1648_, v_kind_1649_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1660_) == 0)
{
return v___x_1660_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(lean_object* v_name_1669_, lean_object* v_type_1670_, lean_object* v_val_1671_, lean_object* v_k_1672_, lean_object* v_nondep_1673_, lean_object* v_kind_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v_nondep_boxed_1684_; uint8_t v_kind_boxed_1685_; lean_object* v_res_1686_; 
v_nondep_boxed_1684_ = lean_unbox(v_nondep_1673_);
v_kind_boxed_1685_ = lean_unbox(v_kind_1674_);
v_res_1686_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1669_, v_type_1670_, v_val_1671_, v_k_1672_, v_nondep_boxed_1684_, v_kind_boxed_1685_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v_ngen_1690_; lean_object* v_namePrefix_1691_; lean_object* v_idx_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1721_; 
v___x_1689_ = lean_st_ref_get(v___y_1687_);
v_ngen_1690_ = lean_ctor_get(v___x_1689_, 2);
lean_inc_ref(v_ngen_1690_);
lean_dec(v___x_1689_);
v_namePrefix_1691_ = lean_ctor_get(v_ngen_1690_, 0);
v_idx_1692_ = lean_ctor_get(v_ngen_1690_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_ngen_1690_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1694_ = v_ngen_1690_;
v_isShared_1695_ = v_isSharedCheck_1721_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_idx_1692_);
lean_inc(v_namePrefix_1691_);
lean_dec(v_ngen_1690_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1721_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v_env_1697_; lean_object* v_nextMacroScope_1698_; lean_object* v_auxDeclNGen_1699_; lean_object* v_traceState_1700_; lean_object* v_cache_1701_; lean_object* v_messages_1702_; lean_object* v_infoState_1703_; lean_object* v_snapshotTasks_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1719_; 
v___x_1696_ = lean_st_ref_take(v___y_1687_);
v_env_1697_ = lean_ctor_get(v___x_1696_, 0);
v_nextMacroScope_1698_ = lean_ctor_get(v___x_1696_, 1);
v_auxDeclNGen_1699_ = lean_ctor_get(v___x_1696_, 3);
v_traceState_1700_ = lean_ctor_get(v___x_1696_, 4);
v_cache_1701_ = lean_ctor_get(v___x_1696_, 5);
v_messages_1702_ = lean_ctor_get(v___x_1696_, 6);
v_infoState_1703_ = lean_ctor_get(v___x_1696_, 7);
v_snapshotTasks_1704_ = lean_ctor_get(v___x_1696_, 8);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v___x_1696_, 2);
lean_dec(v_unused_1720_);
v___x_1706_ = v___x_1696_;
v_isShared_1707_ = v_isSharedCheck_1719_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_snapshotTasks_1704_);
lean_inc(v_infoState_1703_);
lean_inc(v_messages_1702_);
lean_inc(v_cache_1701_);
lean_inc(v_traceState_1700_);
lean_inc(v_auxDeclNGen_1699_);
lean_inc(v_nextMacroScope_1698_);
lean_inc(v_env_1697_);
lean_dec(v___x_1696_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1719_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_r_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_inc(v_idx_1692_);
lean_inc(v_namePrefix_1691_);
v_r_1708_ = l_Lean_Name_num___override(v_namePrefix_1691_, v_idx_1692_);
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_nat_add(v_idx_1692_, v___x_1709_);
lean_dec(v_idx_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1710_);
v___x_1712_ = v___x_1694_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_namePrefix_1691_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 2, v___x_1712_);
v___x_1714_ = v___x_1706_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_env_1697_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_nextMacroScope_1698_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_auxDeclNGen_1699_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_traceState_1700_);
lean_ctor_set(v_reuseFailAlloc_1717_, 5, v_cache_1701_);
lean_ctor_set(v_reuseFailAlloc_1717_, 6, v_messages_1702_);
lean_ctor_set(v_reuseFailAlloc_1717_, 7, v_infoState_1703_);
lean_ctor_set(v_reuseFailAlloc_1717_, 8, v_snapshotTasks_1704_);
v___x_1714_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_st_ref_set(v___y_1687_, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_r_1708_);
return v___x_1716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1722_);
lean_dec(v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(lean_object* v_body_1725_, lean_object* v_u_1726_, lean_object* v_00_u03c3s_1727_, lean_object* v_hyps_1728_, lean_object* v_k_1729_, lean_object* v_val_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_expr_instantiate1(v_body_1725_, v_val_1730_);
v___x_1741_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1741_, 0, v_u_1726_);
lean_ctor_set(v___x_1741_, 1, v_00_u03c3s_1727_);
lean_ctor_set(v___x_1741_, 2, v_hyps_1728_);
lean_ctor_set(v___x_1741_, 3, v___x_1740_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
v___x_1742_ = lean_apply_10(v_k_1729_, v___x_1741_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, lean_box(0));
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_mk_empty_array_with_capacity(v___x_1744_);
v___x_1746_ = lean_array_push(v___x_1745_, v_val_1730_);
v___x_1747_ = 1;
v___x_1748_ = 1;
v___x_1749_ = l_Lean_Meta_mkLetFVars(v___x_1746_, v_a_1743_, v___x_1747_, v___x_1747_, v___x_1748_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1746_);
return v___x_1749_;
}
else
{
lean_dec_ref(v_val_1730_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(lean_object* v_body_1750_, lean_object* v_u_1751_, lean_object* v_00_u03c3s_1752_, lean_object* v_hyps_1753_, lean_object* v_k_1754_, lean_object* v_val_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_1750_, v_u_1751_, v_00_u03c3s_1752_, v_hyps_1753_, v_k_1754_, v_val_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v_body_1750_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(lean_object* v_goal_1773_, lean_object* v_ident_1774_, lean_object* v_k_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_u_1785_; lean_object* v_00_u03c3s_1786_; lean_object* v_hyps_1787_; lean_object* v_target_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1899_; 
v_u_1785_ = lean_ctor_get(v_goal_1773_, 0);
v_00_u03c3s_1786_ = lean_ctor_get(v_goal_1773_, 1);
v_hyps_1787_ = lean_ctor_get(v_goal_1773_, 2);
v_target_1788_ = lean_ctor_get(v_goal_1773_, 3);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_goal_1773_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1790_ = v_goal_1773_;
v_isShared_1791_ = v_isSharedCheck_1899_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_target_1788_);
lean_inc(v_hyps_1787_);
lean_inc(v_00_u03c3s_1786_);
lean_inc(v_u_1785_);
lean_dec(v_goal_1773_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1899_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_1793_ = lean_unsigned_to_nat(3u);
v___x_1794_ = l_Lean_Expr_isAppOfArity(v_target_1788_, v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_del_object(v___x_1790_);
if (lean_obj_tag(v_target_1788_) == 8)
{
lean_object* v_declName_1795_; lean_object* v_type_1796_; lean_object* v_value_1797_; lean_object* v_body_1798_; lean_object* v___f_1799_; lean_object* v_name_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_declName_1795_ = lean_ctor_get(v_target_1788_, 0);
lean_inc(v_declName_1795_);
v_type_1796_ = lean_ctor_get(v_target_1788_, 1);
lean_inc_ref(v_type_1796_);
v_value_1797_ = lean_ctor_get(v_target_1788_, 2);
lean_inc_ref(v_value_1797_);
v_body_1798_ = lean_ctor_get(v_target_1788_, 3);
lean_inc_ref(v_body_1798_);
lean_dec_ref_known(v_target_1788_, 4);
v___f_1799_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed), 15, 5);
lean_closure_set(v___f_1799_, 0, v_body_1798_);
lean_closure_set(v___f_1799_, 1, v_u_1785_);
lean_closure_set(v___f_1799_, 2, v_00_u03c3s_1786_);
lean_closure_set(v___f_1799_, 3, v_hyps_1787_);
lean_closure_set(v___f_1799_, 4, v_k_1775_);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1774_);
v___x_1813_ = l_Lean_Syntax_isOfKind(v_ident_1774_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
lean_dec(v_ident_1774_);
v___x_1814_ = l_Lean_Core_mkFreshUserName(v_declName_1795_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v_name_1801_ = v_a_1815_;
v___y_1802_ = v___y_1776_;
v___y_1803_ = v___y_1777_;
v___y_1804_ = v___y_1778_;
v___y_1805_ = v___y_1779_;
v___y_1806_ = v___y_1780_;
v___y_1807_ = v___y_1781_;
v___y_1808_ = v___y_1782_;
v___y_1809_ = v___y_1783_;
goto v___jp_1800_;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v___f_1799_);
lean_dec_ref(v_value_1797_);
lean_dec_ref(v_type_1796_);
v_a_1816_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1814_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v___x_1824_; lean_object* v_name_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v_name_1825_ = l_Lean_Syntax_getArg(v_ident_1774_, v___x_1824_);
lean_dec(v_ident_1774_);
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_1825_);
v___x_1827_ = l_Lean_Syntax_isOfKind(v_name_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec(v_name_1825_);
v___x_1828_ = l_Lean_Core_mkFreshUserName(v_declName_1795_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v_name_1801_ = v_a_1829_;
v___y_1802_ = v___y_1776_;
v___y_1803_ = v___y_1777_;
v___y_1804_ = v___y_1778_;
v___y_1805_ = v___y_1779_;
v___y_1806_ = v___y_1780_;
v___y_1807_ = v___y_1781_;
v___y_1808_ = v___y_1782_;
v___y_1809_ = v___y_1783_;
goto v___jp_1800_;
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v___f_1799_);
lean_dec_ref(v_value_1797_);
lean_dec_ref(v_type_1796_);
v_a_1830_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1828_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1828_);
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
lean_object* v___x_1838_; 
lean_dec(v_declName_1795_);
v___x_1838_ = l_Lean_TSyntax_getId(v_name_1825_);
lean_dec(v_name_1825_);
v_name_1801_ = v___x_1838_;
v___y_1802_ = v___y_1776_;
v___y_1803_ = v___y_1777_;
v___y_1804_ = v___y_1778_;
v___y_1805_ = v___y_1779_;
v___y_1806_ = v___y_1780_;
v___y_1807_ = v___y_1781_;
v___y_1808_ = v___y_1782_;
v___y_1809_ = v___y_1783_;
goto v___jp_1800_;
}
}
v___jp_1800_:
{
uint8_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = 0;
v___x_1811_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1801_, v_type_1796_, v_value_1797_, v___f_1799_, v___x_1794_, v___x_1810_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1811_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref(v_hyps_1787_);
lean_dec_ref(v_00_u03c3s_1786_);
lean_dec(v_u_1785_);
lean_dec_ref(v_k_1775_);
lean_dec(v_ident_1774_);
v___x_1839_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_1840_ = l_Lean_MessageData_ofExpr(v_target_1788_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1841_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
return v___x_1842_;
}
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_1774_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___x_1847_; lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_hyp_1853_; lean_object* v___x_1854_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v_fst_1845_ = lean_ctor_get(v_a_1844_, 0);
lean_inc(v_fst_1845_);
v_snd_1846_ = lean_ctor_get(v_a_1844_, 1);
lean_inc(v_snd_1846_);
lean_dec(v_a_1844_);
v___x_1847_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1783_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = l_Lean_Expr_appFn_x21(v_target_1788_);
v___x_1850_ = l_Lean_Expr_appFn_x21(v___x_1849_);
v___x_1851_ = l_Lean_Expr_appArg_x21(v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = l_Lean_Expr_appArg_x21(v___x_1849_);
lean_dec_ref(v___x_1849_);
v_hyp_1853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_1853_, 0, v_fst_1845_);
lean_ctor_set(v_hyp_1853_, 1, v_a_1848_);
lean_ctor_set(v_hyp_1853_, 2, v___x_1852_);
lean_inc_ref(v_hyp_1853_);
lean_inc_ref(v___x_1851_);
v___x_1854_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1846_, v___x_1851_, v_hyp_1853_, v___x_1794_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_H_1855_; lean_object* v___x_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref_known(v___x_1854_, 1);
v_H_1855_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_1853_);
lean_inc_ref(v_H_1855_);
lean_inc_ref(v_hyps_1787_);
lean_inc_ref(v_00_u03c3s_1786_);
lean_inc(v_u_1785_);
v___x_1856_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_1785_, v_00_u03c3s_1786_, v_hyps_1787_, v_H_1855_);
v_fst_1857_ = lean_ctor_get(v___x_1856_, 0);
v_snd_1858_ = lean_ctor_get(v___x_1856_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1860_ = v___x_1856_;
v_isShared_1861_ = v_isSharedCheck_1882_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
lean_dec(v___x_1856_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1882_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = l_Lean_Expr_appArg_x21(v_target_1788_);
lean_dec_ref(v_target_1788_);
lean_inc_ref(v___x_1862_);
lean_inc(v_fst_1857_);
lean_inc(v_u_1785_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 3, v___x_1862_);
lean_ctor_set(v___x_1790_, 2, v_fst_1857_);
v___x_1864_ = v___x_1790_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_u_1785_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_00_u03c3s_1786_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_fst_1857_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1778_);
lean_inc(v___y_1777_);
lean_inc_ref(v___y_1776_);
v___x_1865_ = lean_apply_10(v_k_1775_, v___x_1864_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, lean_box(0));
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1880_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1880_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1880_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0));
v___x_1871_ = lean_box(0);
if (v_isShared_1861_ == 0)
{
lean_ctor_set_tag(v___x_1860_, 1);
lean_ctor_set(v___x_1860_, 1, v___x_1871_);
lean_ctor_set(v___x_1860_, 0, v_u_1785_);
v___x_1873_ = v___x_1860_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_u_1785_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v_prf_1875_; lean_object* v___x_1877_; 
v___x_1874_ = l_Lean_mkConst(v___x_1870_, v___x_1873_);
v_prf_1875_ = l_Lean_mkApp7(v___x_1874_, v___x_1851_, v_fst_1857_, v_hyps_1787_, v_H_1855_, v___x_1862_, v_snd_1858_, v_a_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v_prf_1875_);
v___x_1877_ = v___x_1868_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_prf_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_dec_ref(v___x_1862_);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec_ref(v_H_1855_);
lean_dec_ref(v___x_1851_);
lean_dec_ref(v_hyps_1787_);
lean_dec(v_u_1785_);
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref_known(v_hyp_1853_, 3);
lean_dec_ref(v___x_1851_);
lean_del_object(v___x_1790_);
lean_dec_ref(v_target_1788_);
lean_dec_ref(v_hyps_1787_);
lean_dec_ref(v_00_u03c3s_1786_);
lean_dec(v_u_1785_);
lean_dec_ref(v_k_1775_);
v_a_1883_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1854_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1854_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_del_object(v___x_1790_);
lean_dec_ref(v_target_1788_);
lean_dec_ref(v_hyps_1787_);
lean_dec_ref(v_00_u03c3s_1786_);
lean_dec(v_u_1785_);
lean_dec_ref(v_k_1775_);
v_a_1891_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1843_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1843_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(lean_object* v_goal_1900_, lean_object* v_ident_1901_, lean_object* v_k_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_1900_, v_ident_1901_, v_k_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(lean_object* v___x_1913_, lean_object* v_snd_1914_, lean_object* v_ident_1915_, lean_object* v_fst_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; lean_object* v___f_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_st_mk_ref(v___x_1913_);
lean_inc(v___x_1926_);
v___f_1927_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1927_, 0, v___x_1926_);
v___x_1928_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_snd_1914_, v_ident_1915_, v___f_1927_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1916_, v_a_1929_, v___y_1922_);
lean_dec_ref(v___x_1930_);
v___x_1931_ = lean_st_ref_get(v___x_1926_);
lean_dec(v___x_1926_);
v___x_1932_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1931_, v___y_1918_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
return v___x_1932_;
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v___x_1926_);
lean_dec(v_fst_1916_);
v_a_1933_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1928_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1928_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed(lean_object* v___x_1941_, lean_object* v_snd_1942_, lean_object* v_ident_1943_, lean_object* v_fst_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(v___x_1941_, v_snd_1942_, v_ident_1943_, v_fst_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(lean_object* v_x_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_1961_);
v___x_1972_ = l_Lean_Syntax_isOfKind(v_x_1961_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec(v_x_1961_);
v___x_1973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = l_Lean_Syntax_getArg(v_x_1961_, v___x_1974_);
lean_dec(v_x_1961_);
lean_inc(v___x_1975_);
v___x_1976_ = l_Lean_Syntax_matchesNull(v___x_1975_, v___x_1974_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec(v___x_1975_);
v___x_1977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = l_Lean_Syntax_getArg(v___x_1975_, v___x_1978_);
lean_dec(v___x_1975_);
v___x_1980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_1979_);
v___x_1981_ = l_Lean_Syntax_isOfKind(v___x_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1));
lean_inc(v___x_1979_);
v___x_1983_ = l_Lean_Syntax_isOfKind(v___x_1979_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec(v___x_1979_);
v___x_1984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1984_;
}
else
{
lean_object* v_ident_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_ident_1985_ = l_Lean_Syntax_getArg(v___x_1979_, v___x_1974_);
lean_dec(v___x_1979_);
v___x_1986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1985_);
v___x_1987_ = l_Lean_Syntax_isOfKind(v_ident_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec(v_ident_1985_);
v___x_1988_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1963_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v_fst_1991_; lean_object* v_snd_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v_fst_1991_ = lean_ctor_get(v_a_1990_, 0);
lean_inc_n(v_fst_1991_, 2);
v_snd_1992_ = lean_ctor_get(v_a_1990_, 1);
lean_inc(v_snd_1992_);
lean_dec(v_a_1990_);
v___x_1993_ = lean_box(0);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1994_, 0, v___x_1993_);
lean_closure_set(v___f_1994_, 1, v_snd_1992_);
lean_closure_set(v___f_1994_, 2, v_ident_1985_);
lean_closure_set(v___f_1994_, 3, v_fst_1991_);
v___x_1995_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_1991_, v___f_1994_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_1995_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_ident_1985_);
v_a_1996_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1989_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1989_);
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
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = l_Lean_Syntax_getArg(v___x_1979_, v___x_1978_);
lean_dec(v___x_1979_);
v___x_2005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_2004_);
v___x_2006_ = l_Lean_Syntax_isOfKind(v___x_2004_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_dec(v___x_2004_);
v___x_2007_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2007_;
}
else
{
lean_object* v_ident_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_ident_2008_ = l_Lean_Syntax_getArg(v___x_2004_, v___x_1978_);
lean_dec(v___x_2004_);
v___x_2009_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_2008_);
v___x_2010_ = l_Lean_Syntax_isOfKind(v_ident_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec(v_ident_2008_);
v___x_2011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2011_;
}
else
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1963_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v_fst_2014_ = lean_ctor_get(v_a_2013_, 0);
lean_inc_n(v_fst_2014_, 2);
v_snd_2015_ = lean_ctor_get(v_a_2013_, 1);
lean_inc(v_snd_2015_);
lean_dec(v_a_2013_);
v___x_2016_ = lean_box(0);
v___f_2017_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2017_, 0, v___x_2016_);
lean_closure_set(v___f_2017_, 1, v_snd_2015_);
lean_closure_set(v___f_2017_, 2, v_ident_2008_);
lean_closure_set(v___f_2017_, 3, v_fst_2014_);
v___x_2018_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2014_, v___f_2017_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_2018_;
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_ident_2008_);
v_a_2019_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2012_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2012_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(lean_object* v_x_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(v_x_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(lean_object* v_mvarId_2038_, lean_object* v_val_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_2038_, v_val_2039_, v___y_2045_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(lean_object* v_mvarId_2050_, lean_object* v_val_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(v_mvarId_2050_, v_val_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_object* v_00_u03b1_2062_, lean_object* v_name_2063_, lean_object* v_type_2064_, lean_object* v_val_2065_, lean_object* v_k_2066_, uint8_t v_nondep_2067_, uint8_t v_kind_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_2063_, v_type_2064_, v_val_2065_, v_k_2066_, v_nondep_2067_, v_kind_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2079_, lean_object* v_name_2080_, lean_object* v_type_2081_, lean_object* v_val_2082_, lean_object* v_k_2083_, lean_object* v_nondep_2084_, lean_object* v_kind_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v_nondep_boxed_2095_; uint8_t v_kind_boxed_2096_; lean_object* v_res_2097_; 
v_nondep_boxed_2095_ = lean_unbox(v_nondep_2084_);
v_kind_boxed_2096_ = lean_unbox(v_kind_2085_);
v_res_2097_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(v_00_u03b1_2079_, v_name_2080_, v_type_2081_, v_val_2082_, v_k_2083_, v_nondep_boxed_2095_, v_kind_boxed_2096_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_object* v_00_u03b1_2110_, lean_object* v_msg_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2118_, lean_object* v_msg_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(v_00_u03b1_2118_, v_msg_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2126_, lean_object* v_name_2127_, uint8_t v_bi_2128_, lean_object* v_type_2129_, lean_object* v_k_2130_, uint8_t v_kind_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_2127_, v_bi_2128_, v_type_2129_, v_k_2130_, v_kind_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_name_2139_, lean_object* v_bi_2140_, lean_object* v_type_2141_, lean_object* v_k_2142_, lean_object* v_kind_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v_bi_boxed_2149_; uint8_t v_kind_boxed_2150_; lean_object* v_res_2151_; 
v_bi_boxed_2149_ = lean_unbox(v_bi_2140_);
v_kind_boxed_2150_ = lean_unbox(v_kind_2143_);
v_res_2151_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(v_00_u03b1_2138_, v_name_2139_, v_bi_boxed_2149_, v_type_2141_, v_k_2142_, v_kind_boxed_2150_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_object* v_00_u03b1_2152_, lean_object* v_name_2153_, lean_object* v_type_2154_, lean_object* v_k_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_2153_, v_type_2154_, v_k_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_name_2163_, lean_object* v_type_2164_, lean_object* v_k_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(v_00_u03b1_2162_, v_name_2163_, v_type_2164_, v_k_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(lean_object* v_00_u03b2_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_x_2173_, v_x_2174_, v_x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2177_, lean_object* v_x_2178_, size_t v_x_2179_, size_t v_x_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_2178_, v_x_2179_, v_x_2180_, v_x_2181_, v_x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
size_t v_x_21850__boxed_2190_; size_t v_x_21851__boxed_2191_; lean_object* v_res_2192_; 
v_x_21850__boxed_2190_ = lean_unbox_usize(v_x_2186_);
lean_dec(v_x_2186_);
v_x_21851__boxed_2191_ = lean_unbox_usize(v_x_2187_);
lean_dec(v_x_2187_);
v_res_2192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(v_00_u03b2_2184_, v_x_2185_, v_x_21850__boxed_2190_, v_x_21851__boxed_2191_, v_x_2188_, v_x_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2193_, lean_object* v_n_2194_, lean_object* v_k_2195_, lean_object* v_v_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v_n_2194_, v_k_2195_, v_v_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b2_2198_, size_t v_depth_2199_, lean_object* v_keys_2200_, lean_object* v_vals_2201_, lean_object* v_heq_2202_, lean_object* v_i_2203_, lean_object* v_entries_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_2199_, v_keys_2200_, v_vals_2201_, v_i_2203_, v_entries_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b2_2206_, lean_object* v_depth_2207_, lean_object* v_keys_2208_, lean_object* v_vals_2209_, lean_object* v_heq_2210_, lean_object* v_i_2211_, lean_object* v_entries_2212_){
_start:
{
size_t v_depth_boxed_2213_; lean_object* v_res_2214_; 
v_depth_boxed_2213_ = lean_unbox_usize(v_depth_2207_);
lean_dec(v_depth_2207_);
v_res_2214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(v_00_u03b2_2206_, v_depth_boxed_2213_, v_keys_2208_, v_vals_2209_, v_heq_2210_, v_i_2211_, v_entries_2212_);
lean_dec_ref(v_vals_2209_);
lean_dec_ref(v_keys_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_x_2216_, v_x_2217_, v_x_2218_, v_x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1(){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2233_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_2234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3));
v___x_2235_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed), 10, 0);
v___x_2236_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2232_, v___x_2233_, v___x_2234_, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
return v_res_2238_;
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
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
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
