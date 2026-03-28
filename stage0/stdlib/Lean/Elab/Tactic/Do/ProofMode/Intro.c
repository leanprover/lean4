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
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMIntro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
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
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_319_);
v_declName_340_ = lean_ctor_get(v_target_333_, 0);
lean_inc(v_declName_340_);
v_type_341_ = lean_ctor_get(v_target_333_, 1);
lean_inc_ref(v_type_341_);
v_value_342_ = lean_ctor_get(v_target_333_, 2);
lean_inc_ref(v_value_342_);
v_body_343_ = lean_ctor_get(v_target_333_, 3);
lean_inc_ref(v_body_343_);
lean_dec_ref(v_target_333_);
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
lean_dec_ref(v___x_326_);
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
lean_dec_ref(v___x_467_);
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
lean_dec_ref(v___x_540_);
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
lean_dec_ref(v___x_559_);
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
lean_dec_ref(v___x_576_);
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
lean_dec_ref(v___x_932_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; 
v___x_1137_ = ((size_t)5ULL);
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_shift_left(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0);
v___x_1142_ = lean_usize_sub(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(lean_object* v_x_1144_, size_t v_x_1145_, size_t v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
if (lean_obj_tag(v_x_1144_) == 0)
{
lean_object* v_es_1149_; size_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v_j_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_es_1149_ = lean_ctor_get(v_x_1144_, 0);
v___x_1150_ = ((size_t)5ULL);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1);
v___x_1153_ = lean_usize_land(v_x_1145_, v___x_1152_);
v_j_1154_ = lean_usize_to_nat(v___x_1153_);
v___x_1155_ = lean_array_get_size(v_es_1149_);
v___x_1156_ = lean_nat_dec_lt(v_j_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec(v_j_1154_);
lean_dec(v_x_1148_);
lean_dec(v_x_1147_);
return v_x_1144_;
}
else
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1193_; 
lean_inc_ref(v_es_1149_);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_x_1144_, 0);
lean_dec(v_unused_1194_);
v___x_1158_ = v_x_1144_;
v_isShared_1159_ = v_isSharedCheck_1193_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v_x_1144_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1193_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_v_1160_; lean_object* v___x_1161_; lean_object* v_xs_x27_1162_; lean_object* v___y_1164_; 
v_v_1160_ = lean_array_fget(v_es_1149_, v_j_1154_);
v___x_1161_ = lean_box(0);
v_xs_x27_1162_ = lean_array_fset(v_es_1149_, v_j_1154_, v___x_1161_);
switch(lean_obj_tag(v_v_1160_))
{
case 0:
{
lean_object* v_key_1169_; lean_object* v_val_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v_key_1169_ = lean_ctor_get(v_v_1160_, 0);
v_val_1170_ = lean_ctor_get(v_v_1160_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_v_1160_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1172_ = v_v_1160_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_val_1170_);
lean_inc(v_key_1169_);
lean_dec(v_v_1160_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
uint8_t v___x_1174_; 
v___x_1174_ = l_Lean_instBEqMVarId_beq(v_x_1147_, v_key_1169_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_del_object(v___x_1172_);
v___x_1175_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1169_, v_val_1170_, v_x_1147_, v_x_1148_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
v___y_1164_ = v___x_1176_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1178_; 
lean_dec(v_val_1170_);
lean_dec(v_key_1169_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_x_1148_);
lean_ctor_set(v___x_1172_, 0, v_x_1147_);
v___x_1178_ = v___x_1172_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_x_1147_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_x_1148_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
v___y_1164_ = v___x_1178_;
goto v___jp_1163_;
}
}
}
}
case 1:
{
lean_object* v_node_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_node_1181_ = lean_ctor_get(v_v_1160_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_v_1160_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1183_ = v_v_1160_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_node_1181_);
lean_dec(v_v_1160_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1185_ = lean_usize_shift_right(v_x_1145_, v___x_1150_);
v___x_1186_ = lean_usize_add(v_x_1146_, v___x_1151_);
v___x_1187_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_node_1181_, v___x_1185_, v___x_1186_, v_x_1147_, v_x_1148_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1187_);
v___x_1189_ = v___x_1183_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v___y_1164_ = v___x_1189_;
goto v___jp_1163_;
}
}
}
default: 
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_x_1147_);
lean_ctor_set(v___x_1192_, 1, v_x_1148_);
v___y_1164_ = v___x_1192_;
goto v___jp_1163_;
}
}
v___jp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_array_fset(v_xs_x27_1162_, v_j_1154_, v___y_1164_);
lean_dec(v_j_1154_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1165_);
v___x_1167_ = v___x_1158_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
else
{
lean_object* v_ks_1195_; lean_object* v_vs_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1216_; 
v_ks_1195_ = lean_ctor_get(v_x_1144_, 0);
v_vs_1196_ = lean_ctor_get(v_x_1144_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1198_ = v_x_1144_;
v_isShared_1199_ = v_isSharedCheck_1216_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_vs_1196_);
lean_inc(v_ks_1195_);
lean_dec(v_x_1144_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1216_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_ks_1195_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_vs_1196_);
v___x_1201_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v_newNode_1202_; uint8_t v___y_1204_; size_t v___x_1210_; uint8_t v___x_1211_; 
v_newNode_1202_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v___x_1201_, v_x_1147_, v_x_1148_);
v___x_1210_ = ((size_t)7ULL);
v___x_1211_ = lean_usize_dec_le(v___x_1210_, v_x_1146_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1202_);
v___x_1213_ = lean_unsigned_to_nat(4u);
v___x_1214_ = lean_nat_dec_lt(v___x_1212_, v___x_1213_);
lean_dec(v___x_1212_);
v___y_1204_ = v___x_1214_;
goto v___jp_1203_;
}
else
{
v___y_1204_ = v___x_1211_;
goto v___jp_1203_;
}
v___jp_1203_:
{
if (v___y_1204_ == 0)
{
lean_object* v_ks_1205_; lean_object* v_vs_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_ks_1205_ = lean_ctor_get(v_newNode_1202_, 0);
lean_inc_ref(v_ks_1205_);
v_vs_1206_ = lean_ctor_get(v_newNode_1202_, 1);
lean_inc_ref(v_vs_1206_);
lean_dec_ref(v_newNode_1202_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2);
v___x_1209_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_x_1146_, v_ks_1205_, v_vs_1206_, v___x_1207_, v___x_1208_);
lean_dec_ref(v_vs_1206_);
lean_dec_ref(v_ks_1205_);
return v___x_1209_;
}
else
{
return v_newNode_1202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(size_t v_depth_1217_, lean_object* v_keys_1218_, lean_object* v_vals_1219_, lean_object* v_i_1220_, lean_object* v_entries_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_array_get_size(v_keys_1218_);
v___x_1223_ = lean_nat_dec_lt(v_i_1220_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec(v_i_1220_);
return v_entries_1221_;
}
else
{
lean_object* v_k_1224_; lean_object* v_v_1225_; uint64_t v___x_1226_; size_t v_h_1227_; size_t v___x_1228_; lean_object* v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v_h_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_k_1224_ = lean_array_fget_borrowed(v_keys_1218_, v_i_1220_);
v_v_1225_ = lean_array_fget_borrowed(v_vals_1219_, v_i_1220_);
v___x_1226_ = l_Lean_instHashableMVarId_hash(v_k_1224_);
v_h_1227_ = lean_uint64_to_usize(v___x_1226_);
v___x_1228_ = ((size_t)5ULL);
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_sub(v_depth_1217_, v___x_1230_);
v___x_1232_ = lean_usize_mul(v___x_1228_, v___x_1231_);
v_h_1233_ = lean_usize_shift_right(v_h_1227_, v___x_1232_);
v___x_1234_ = lean_nat_add(v_i_1220_, v___x_1229_);
lean_dec(v_i_1220_);
lean_inc(v_v_1225_);
lean_inc(v_k_1224_);
v___x_1235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_entries_1221_, v_h_1233_, v_depth_1217_, v_k_1224_, v_v_1225_);
v_i_1220_ = v___x_1234_;
v_entries_1221_ = v___x_1235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_depth_1237_, lean_object* v_keys_1238_, lean_object* v_vals_1239_, lean_object* v_i_1240_, lean_object* v_entries_1241_){
_start:
{
size_t v_depth_boxed_1242_; lean_object* v_res_1243_; 
v_depth_boxed_1242_ = lean_unbox_usize(v_depth_1237_);
lean_dec(v_depth_1237_);
v_res_1243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_boxed_1242_, v_keys_1238_, v_vals_1239_, v_i_1240_, v_entries_1241_);
lean_dec_ref(v_vals_1239_);
lean_dec_ref(v_keys_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
size_t v_x_20306__boxed_1249_; size_t v_x_20307__boxed_1250_; lean_object* v_res_1251_; 
v_x_20306__boxed_1249_ = lean_unbox_usize(v_x_1245_);
lean_dec(v_x_1245_);
v_x_20307__boxed_1250_ = lean_unbox_usize(v_x_1246_);
lean_dec(v_x_1246_);
v_res_1251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1244_, v_x_20306__boxed_1249_, v_x_20307__boxed_1250_, v_x_1247_, v_x_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint64_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = l_Lean_instHashableMVarId_hash(v_x_1253_);
v___x_1256_ = lean_uint64_to_usize(v___x_1255_);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1252_, v___x_1256_, v___x_1257_, v_x_1253_, v_x_1254_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(lean_object* v_mvarId_1259_, lean_object* v_val_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v_mctx_1264_; lean_object* v_cache_1265_; lean_object* v_zetaDeltaFVarIds_1266_; lean_object* v_postponed_1267_; lean_object* v_diag_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1295_; 
v___x_1263_ = lean_st_ref_take(v___y_1261_);
v_mctx_1264_ = lean_ctor_get(v___x_1263_, 0);
v_cache_1265_ = lean_ctor_get(v___x_1263_, 1);
v_zetaDeltaFVarIds_1266_ = lean_ctor_get(v___x_1263_, 2);
v_postponed_1267_ = lean_ctor_get(v___x_1263_, 3);
v_diag_1268_ = lean_ctor_get(v___x_1263_, 4);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1270_ = v___x_1263_;
v_isShared_1271_ = v_isSharedCheck_1295_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_diag_1268_);
lean_inc(v_postponed_1267_);
lean_inc(v_zetaDeltaFVarIds_1266_);
lean_inc(v_cache_1265_);
lean_inc(v_mctx_1264_);
lean_dec(v___x_1263_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1295_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_depth_1272_; lean_object* v_levelAssignDepth_1273_; lean_object* v_mvarCounter_1274_; lean_object* v_lDepth_1275_; lean_object* v_decls_1276_; lean_object* v_userNames_1277_; lean_object* v_lAssignment_1278_; lean_object* v_eAssignment_1279_; lean_object* v_dAssignment_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1294_; 
v_depth_1272_ = lean_ctor_get(v_mctx_1264_, 0);
v_levelAssignDepth_1273_ = lean_ctor_get(v_mctx_1264_, 1);
v_mvarCounter_1274_ = lean_ctor_get(v_mctx_1264_, 2);
v_lDepth_1275_ = lean_ctor_get(v_mctx_1264_, 3);
v_decls_1276_ = lean_ctor_get(v_mctx_1264_, 4);
v_userNames_1277_ = lean_ctor_get(v_mctx_1264_, 5);
v_lAssignment_1278_ = lean_ctor_get(v_mctx_1264_, 6);
v_eAssignment_1279_ = lean_ctor_get(v_mctx_1264_, 7);
v_dAssignment_1280_ = lean_ctor_get(v_mctx_1264_, 8);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_mctx_1264_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1282_ = v_mctx_1264_;
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_dAssignment_1280_);
lean_inc(v_eAssignment_1279_);
lean_inc(v_lAssignment_1278_);
lean_inc(v_userNames_1277_);
lean_inc(v_decls_1276_);
lean_inc(v_lDepth_1275_);
lean_inc(v_mvarCounter_1274_);
lean_inc(v_levelAssignDepth_1273_);
lean_inc(v_depth_1272_);
lean_dec(v_mctx_1264_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_eAssignment_1279_, v_mvarId_1259_, v_val_1260_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 7, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_depth_1272_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_levelAssignDepth_1273_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_mvarCounter_1274_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_lDepth_1275_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_decls_1276_);
lean_ctor_set(v_reuseFailAlloc_1293_, 5, v_userNames_1277_);
lean_ctor_set(v_reuseFailAlloc_1293_, 6, v_lAssignment_1278_);
lean_ctor_set(v_reuseFailAlloc_1293_, 7, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1293_, 8, v_dAssignment_1280_);
v___x_1286_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1286_);
v___x_1288_ = v___x_1270_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_cache_1265_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_zetaDeltaFVarIds_1266_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_postponed_1267_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_diag_1268_);
v___x_1288_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_st_ref_set(v___y_1261_, v___x_1288_);
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(lean_object* v_mvarId_1296_, lean_object* v_val_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_1296_, v_val_1297_, v___y_1298_);
lean_dec(v___y_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_k_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
v___x_1308_ = lean_apply_6(v_k_1301_, v_b_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_k_1309_, lean_object* v_b_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_1309_, v_b_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(lean_object* v_name_1317_, uint8_t v_bi_1318_, lean_object* v_type_1319_, lean_object* v_k_1320_, uint8_t v_kind_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1327_, 0, v_k_1320_);
v___x_1328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1317_, v_bi_1318_, v_type_1319_, v___f_1327_, v_kind_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_name_1345_, lean_object* v_bi_1346_, lean_object* v_type_1347_, lean_object* v_k_1348_, lean_object* v_kind_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_bi_boxed_1355_; uint8_t v_kind_boxed_1356_; lean_object* v_res_1357_; 
v_bi_boxed_1355_ = lean_unbox(v_bi_1346_);
v_kind_boxed_1356_ = lean_unbox(v_kind_1349_);
v_res_1357_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1345_, v_bi_boxed_1355_, v_type_1347_, v_k_1348_, v_kind_boxed_1356_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(lean_object* v_name_1358_, lean_object* v_type_1359_, lean_object* v_k_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = 0;
v___x_1367_ = 0;
v___x_1368_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1358_, v___x_1366_, v_type_1359_, v_k_1360_, v___x_1367_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(lean_object* v_name_1369_, lean_object* v_type_1370_, lean_object* v_k_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_1369_, v_type_1370_, v_k_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(lean_object* v_msgData_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v_env_1385_; lean_object* v___x_1386_; lean_object* v_mctx_1387_; lean_object* v_lctx_1388_; lean_object* v_options_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1384_ = lean_st_ref_get(v___y_1382_);
v_env_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc_ref(v_env_1385_);
lean_dec(v___x_1384_);
v___x_1386_ = lean_st_ref_get(v___y_1380_);
v_mctx_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_ref(v_mctx_1387_);
lean_dec(v___x_1386_);
v_lctx_1388_ = lean_ctor_get(v___y_1379_, 2);
v_options_1389_ = lean_ctor_get(v___y_1381_, 2);
lean_inc_ref(v_options_1389_);
lean_inc_ref(v_lctx_1388_);
v___x_1390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1390_, 0, v_env_1385_);
lean_ctor_set(v___x_1390_, 1, v_mctx_1387_);
lean_ctor_set(v___x_1390_, 2, v_lctx_1388_);
lean_ctor_set(v___x_1390_, 3, v_options_1389_);
v___x_1391_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_msgData_1378_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(lean_object* v_msg_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_ref_1406_; lean_object* v___x_1407_; lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1416_; 
v_ref_1406_ = lean_ctor_get(v___y_1403_, 5);
v___x_1407_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msg_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_inc(v_ref_1406_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_ref_1406_);
lean_ctor_set(v___x_1412_, 1, v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 1);
lean_ctor_set(v___x_1410_, 0, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(lean_object* v___x_1424_, lean_object* v_ident_1425_, uint8_t v___x_1426_, lean_object* v_hyps_1427_, lean_object* v___x_1428_, lean_object* v_target_1429_, lean_object* v_u_1430_, lean_object* v_k_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v_s_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_lctx_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_lctx_1442_ = lean_ctor_get(v___y_1437_, 2);
lean_inc_ref(v___x_1424_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1424_);
lean_inc_ref(v_s_1436_);
lean_inc_ref(v_lctx_1442_);
v___x_1444_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_1425_, v_lctx_1442_, v_s_1436_, v___x_1443_, v___x_1426_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v___x_1444_);
lean_inc_ref(v_s_1436_);
lean_inc_ref(v_hyps_1427_);
v___x_1445_ = l_Lean_Expr_app___override(v_hyps_1427_, v_s_1436_);
lean_inc_ref_n(v___x_1428_, 2);
v___x_1446_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_1428_, v___x_1445_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_mk_empty_array_with_capacity(v___x_1447_);
v___x_1449_ = lean_array_push(v___x_1448_, v_s_1436_);
v___x_1450_ = 0;
lean_inc_ref(v_target_1429_);
v___x_1451_ = l_Lean_Expr_betaRev(v_target_1429_, v___x_1449_, v___x_1450_, v___x_1450_);
lean_inc(v_u_1430_);
v___x_1452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1452_, 0, v_u_1430_);
lean_ctor_set(v___x_1452_, 1, v___x_1428_);
lean_ctor_set(v___x_1452_, 2, v___x_1446_);
lean_ctor_set(v___x_1452_, 3, v___x_1451_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
v___x_1453_ = lean_apply_10(v_k_1431_, v___x_1452_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, lean_box(0));
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = 1;
v___x_1456_ = l_Lean_Meta_mkLambdaFVars(v___x_1449_, v_a_1454_, v___x_1450_, v___x_1426_, v___x_1450_, v___x_1426_, v___x_1455_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec_ref(v___x_1449_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1469_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1469_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1469_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_u_1430_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_mkConst(v___x_1461_, v___x_1463_);
v___x_1465_ = l_Lean_mkApp5(v___x_1464_, v___x_1428_, v___x_1424_, v_hyps_1427_, v_target_1429_, v_a_1457_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1465_);
v___x_1467_ = v___x_1459_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_dec(v_u_1430_);
lean_dec_ref(v_target_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v_hyps_1427_);
lean_dec_ref(v___x_1424_);
return v___x_1456_;
}
}
else
{
lean_dec_ref(v___x_1449_);
lean_dec(v_u_1430_);
lean_dec_ref(v_target_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v_hyps_1427_);
lean_dec_ref(v___x_1424_);
return v___x_1453_;
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_s_1436_);
lean_dec_ref(v_k_1431_);
lean_dec(v_u_1430_);
lean_dec_ref(v_target_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v_hyps_1427_);
lean_dec_ref(v___x_1424_);
v_a_1470_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1444_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1444_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_1478_ = _args[0];
lean_object* v_ident_1479_ = _args[1];
lean_object* v___x_1480_ = _args[2];
lean_object* v_hyps_1481_ = _args[3];
lean_object* v___x_1482_ = _args[4];
lean_object* v_target_1483_ = _args[5];
lean_object* v_u_1484_ = _args[6];
lean_object* v_k_1485_ = _args[7];
lean_object* v___y_1486_ = _args[8];
lean_object* v___y_1487_ = _args[9];
lean_object* v___y_1488_ = _args[10];
lean_object* v___y_1489_ = _args[11];
lean_object* v_s_1490_ = _args[12];
lean_object* v___y_1491_ = _args[13];
lean_object* v___y_1492_ = _args[14];
lean_object* v___y_1493_ = _args[15];
lean_object* v___y_1494_ = _args[16];
lean_object* v___y_1495_ = _args[17];
_start:
{
uint8_t v___x_20685__boxed_1496_; lean_object* v_res_1497_; 
v___x_20685__boxed_1496_ = lean_unbox(v___x_1480_);
v_res_1497_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_1478_, v_ident_1479_, v___x_20685__boxed_1496_, v_hyps_1481_, v___x_1482_, v_target_1483_, v_u_1484_, v_k_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v_s_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(lean_object* v_goal_1498_, lean_object* v_ident_1499_, lean_object* v_k_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___y_1511_; lean_object* v_u_1520_; lean_object* v_00_u03c3s_1521_; lean_object* v_hyps_1522_; lean_object* v_target_1523_; lean_object* v___x_1524_; 
v_u_1520_ = lean_ctor_get(v_goal_1498_, 0);
lean_inc(v_u_1520_);
v_00_u03c3s_1521_ = lean_ctor_get(v_goal_1498_, 1);
lean_inc_ref_n(v_00_u03c3s_1521_, 2);
v_hyps_1522_ = lean_ctor_get(v_goal_1498_, 2);
lean_inc_ref(v_hyps_1522_);
v_target_1523_ = lean_ctor_get(v_goal_1498_, 3);
lean_inc_ref(v_target_1523_);
lean_dec_ref(v_goal_1498_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
v___x_1524_ = lean_whnf(v_00_u03c3s_1521_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_1527_ = lean_unsigned_to_nat(3u);
v___x_1528_ = l_Lean_Expr_isAppOfArity(v_a_1525_, v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_a_1525_);
lean_dec_ref(v_target_1523_);
lean_dec_ref(v_hyps_1522_);
lean_dec(v_u_1520_);
lean_dec_ref(v_k_1500_);
lean_dec(v_ident_1499_);
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_1530_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_1521_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1531_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
v___y_1511_ = v___x_1532_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
lean_dec_ref(v_00_u03c3s_1521_);
v___x_1533_ = l_Lean_Expr_appFn_x21(v_a_1525_);
v___x_1534_ = l_Lean_Expr_appArg_x21(v___x_1533_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = l_Lean_Expr_appArg_x21(v_a_1525_);
lean_dec(v_a_1525_);
v___x_1536_ = lean_box(v___x_1528_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc_n(v_ident_1499_, 2);
lean_inc_ref(v___x_1534_);
v___f_1537_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1537_, 0, v___x_1534_);
lean_closure_set(v___f_1537_, 1, v_ident_1499_);
lean_closure_set(v___f_1537_, 2, v___x_1536_);
lean_closure_set(v___f_1537_, 3, v_hyps_1522_);
lean_closure_set(v___f_1537_, 4, v___x_1535_);
lean_closure_set(v___f_1537_, 5, v_target_1523_);
lean_closure_set(v___f_1537_, 6, v_u_1520_);
lean_closure_set(v___f_1537_, 7, v_k_1500_);
lean_closure_set(v___f_1537_, 8, v___y_1501_);
lean_closure_set(v___f_1537_, 9, v___y_1502_);
lean_closure_set(v___f_1537_, 10, v___y_1503_);
lean_closure_set(v___f_1537_, 11, v___y_1504_);
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_1539_ = l_Lean_Syntax_isOfKind(v_ident_1499_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_ident_1499_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1541_ = l_Lean_Core_mkFreshUserName(v___x_1540_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1542_, v___x_1534_, v___f_1537_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
v___y_1511_ = v___x_1543_;
goto v___jp_1510_;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec_ref(v___f_1537_);
lean_dec_ref(v___x_1534_);
v_a_1544_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1541_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1541_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = l_Lean_Syntax_getArg(v_ident_1499_, v___x_1552_);
lean_dec(v_ident_1499_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_1553_);
v___x_1555_ = l_Lean_Syntax_isOfKind(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v___x_1553_);
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1557_ = l_Lean_Core_mkFreshUserName(v___x_1556_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1558_, v___x_1534_, v___f_1537_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
v___y_1511_ = v___x_1559_;
goto v___jp_1510_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v___f_1537_);
lean_dec_ref(v___x_1534_);
v_a_1560_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1557_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1557_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = l_Lean_TSyntax_getId(v___x_1553_);
lean_dec(v___x_1553_);
v___x_1569_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v___x_1568_, v___x_1534_, v___f_1537_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
v___y_1511_ = v___x_1569_;
goto v___jp_1510_;
}
}
}
}
else
{
lean_dec_ref(v_target_1523_);
lean_dec_ref(v_hyps_1522_);
lean_dec_ref(v_00_u03c3s_1521_);
lean_dec(v_u_1520_);
lean_dec_ref(v_k_1500_);
lean_dec(v_ident_1499_);
return v___x_1524_;
}
v___jp_1510_:
{
if (lean_obj_tag(v___y_1511_) == 0)
{
return v___y_1511_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___y_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___y_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___y_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___y_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(lean_object* v_goal_1570_, lean_object* v_ident_1571_, lean_object* v_k_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_1570_, v_ident_1571_, v_k_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(lean_object* v___x_1583_, lean_object* v_snd_1584_, lean_object* v_ident_1585_, lean_object* v_fst_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_st_mk_ref(v___x_1583_);
lean_inc(v___x_1596_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1597_, 0, v___x_1596_);
v___x_1598_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_snd_1584_, v_ident_1585_, v___f_1597_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1586_, v_a_1599_, v___y_1592_);
lean_dec_ref(v___x_1600_);
v___x_1601_ = lean_st_ref_get(v___x_1596_);
lean_dec(v___x_1596_);
v___x_1602_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1601_, v___y_1588_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1602_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v___x_1596_);
lean_dec(v_fst_1586_);
v_a_1603_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1598_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1598_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(lean_object* v___x_1611_, lean_object* v_snd_1612_, lean_object* v_ident_1613_, lean_object* v_fst_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(v___x_1611_, v_snd_1612_, v_ident_1613_, v_fst_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(lean_object* v_k_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v_b_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
v___x_1636_ = lean_apply_10(v_k_1625_, v_b_1630_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, lean_box(0));
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(lean_object* v_k_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v_b_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(lean_object* v_name_1649_, lean_object* v_type_1650_, lean_object* v_val_1651_, lean_object* v_k_1652_, uint8_t v_nondep_1653_, uint8_t v_kind_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; 
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1664_, 0, v_k_1652_);
lean_closure_set(v___f_1664_, 1, v___y_1655_);
lean_closure_set(v___f_1664_, 2, v___y_1656_);
lean_closure_set(v___f_1664_, 3, v___y_1657_);
lean_closure_set(v___f_1664_, 4, v___y_1658_);
v___x_1665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1649_, v_type_1650_, v_val_1651_, v___f_1664_, v_nondep_1653_, v_kind_1654_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
return v___x_1665_;
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(lean_object* v_name_1674_, lean_object* v_type_1675_, lean_object* v_val_1676_, lean_object* v_k_1677_, lean_object* v_nondep_1678_, lean_object* v_kind_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v_nondep_boxed_1689_; uint8_t v_kind_boxed_1690_; lean_object* v_res_1691_; 
v_nondep_boxed_1689_ = lean_unbox(v_nondep_1678_);
v_kind_boxed_1690_ = lean_unbox(v_kind_1679_);
v_res_1691_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1674_, v_type_1675_, v_val_1676_, v_k_1677_, v_nondep_boxed_1689_, v_kind_boxed_1690_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; lean_object* v_ngen_1695_; lean_object* v_namePrefix_1696_; lean_object* v_idx_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1726_; 
v___x_1694_ = lean_st_ref_get(v___y_1692_);
v_ngen_1695_ = lean_ctor_get(v___x_1694_, 2);
lean_inc_ref(v_ngen_1695_);
lean_dec(v___x_1694_);
v_namePrefix_1696_ = lean_ctor_get(v_ngen_1695_, 0);
v_idx_1697_ = lean_ctor_get(v_ngen_1695_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_ngen_1695_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1699_ = v_ngen_1695_;
v_isShared_1700_ = v_isSharedCheck_1726_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_idx_1697_);
lean_inc(v_namePrefix_1696_);
lean_dec(v_ngen_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1726_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v_env_1702_; lean_object* v_nextMacroScope_1703_; lean_object* v_auxDeclNGen_1704_; lean_object* v_traceState_1705_; lean_object* v_cache_1706_; lean_object* v_messages_1707_; lean_object* v_infoState_1708_; lean_object* v_snapshotTasks_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1724_; 
v___x_1701_ = lean_st_ref_take(v___y_1692_);
v_env_1702_ = lean_ctor_get(v___x_1701_, 0);
v_nextMacroScope_1703_ = lean_ctor_get(v___x_1701_, 1);
v_auxDeclNGen_1704_ = lean_ctor_get(v___x_1701_, 3);
v_traceState_1705_ = lean_ctor_get(v___x_1701_, 4);
v_cache_1706_ = lean_ctor_get(v___x_1701_, 5);
v_messages_1707_ = lean_ctor_get(v___x_1701_, 6);
v_infoState_1708_ = lean_ctor_get(v___x_1701_, 7);
v_snapshotTasks_1709_ = lean_ctor_get(v___x_1701_, 8);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___x_1701_, 2);
lean_dec(v_unused_1725_);
v___x_1711_ = v___x_1701_;
v_isShared_1712_ = v_isSharedCheck_1724_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_snapshotTasks_1709_);
lean_inc(v_infoState_1708_);
lean_inc(v_messages_1707_);
lean_inc(v_cache_1706_);
lean_inc(v_traceState_1705_);
lean_inc(v_auxDeclNGen_1704_);
lean_inc(v_nextMacroScope_1703_);
lean_inc(v_env_1702_);
lean_dec(v___x_1701_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1724_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_r_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
lean_inc(v_idx_1697_);
lean_inc(v_namePrefix_1696_);
v_r_1713_ = l_Lean_Name_num___override(v_namePrefix_1696_, v_idx_1697_);
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_idx_1697_, v___x_1714_);
lean_dec(v_idx_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1715_);
v___x_1717_ = v___x_1699_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_namePrefix_1696_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 2, v___x_1717_);
v___x_1719_ = v___x_1711_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_env_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_nextMacroScope_1703_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_auxDeclNGen_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_traceState_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_cache_1706_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_messages_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_infoState_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_snapshotTasks_1709_);
v___x_1719_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_st_ref_set(v___y_1692_, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_r_1713_);
return v___x_1721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1727_);
lean_dec(v___y_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(lean_object* v_body_1730_, lean_object* v_u_1731_, lean_object* v_00_u03c3s_1732_, lean_object* v_hyps_1733_, lean_object* v_k_1734_, lean_object* v_val_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_expr_instantiate1(v_body_1730_, v_val_1735_);
v___x_1746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1746_, 0, v_u_1731_);
lean_ctor_set(v___x_1746_, 1, v_00_u03c3s_1732_);
lean_ctor_set(v___x_1746_, 2, v_hyps_1733_);
lean_ctor_set(v___x_1746_, 3, v___x_1745_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
lean_inc(v___y_1739_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
v___x_1747_ = lean_apply_10(v_k_1734_, v___x_1746_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_mk_empty_array_with_capacity(v___x_1749_);
v___x_1751_ = lean_array_push(v___x_1750_, v_val_1735_);
v___x_1752_ = 1;
v___x_1753_ = 1;
v___x_1754_ = l_Lean_Meta_mkLetFVars(v___x_1751_, v_a_1748_, v___x_1752_, v___x_1752_, v___x_1753_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec_ref(v___x_1751_);
return v___x_1754_;
}
else
{
lean_dec_ref(v_val_1735_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(lean_object* v_body_1755_, lean_object* v_u_1756_, lean_object* v_00_u03c3s_1757_, lean_object* v_hyps_1758_, lean_object* v_k_1759_, lean_object* v_val_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_1755_, v_u_1756_, v_00_u03c3s_1757_, v_hyps_1758_, v_k_1759_, v_val_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v_body_1755_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(lean_object* v_goal_1778_, lean_object* v_ident_1779_, lean_object* v_k_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_u_1790_; lean_object* v_00_u03c3s_1791_; lean_object* v_hyps_1792_; lean_object* v_target_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1904_; 
v_u_1790_ = lean_ctor_get(v_goal_1778_, 0);
v_00_u03c3s_1791_ = lean_ctor_get(v_goal_1778_, 1);
v_hyps_1792_ = lean_ctor_get(v_goal_1778_, 2);
v_target_1793_ = lean_ctor_get(v_goal_1778_, 3);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_goal_1778_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1795_ = v_goal_1778_;
v_isShared_1796_ = v_isSharedCheck_1904_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_target_1793_);
lean_inc(v_hyps_1792_);
lean_inc(v_00_u03c3s_1791_);
lean_inc(v_u_1790_);
lean_dec(v_goal_1778_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1904_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_1798_ = lean_unsigned_to_nat(3u);
v___x_1799_ = l_Lean_Expr_isAppOfArity(v_target_1793_, v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_del_object(v___x_1795_);
if (lean_obj_tag(v_target_1793_) == 8)
{
lean_object* v_declName_1800_; lean_object* v_type_1801_; lean_object* v_value_1802_; lean_object* v_body_1803_; lean_object* v___f_1804_; lean_object* v_name_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_declName_1800_ = lean_ctor_get(v_target_1793_, 0);
lean_inc(v_declName_1800_);
v_type_1801_ = lean_ctor_get(v_target_1793_, 1);
lean_inc_ref(v_type_1801_);
v_value_1802_ = lean_ctor_get(v_target_1793_, 2);
lean_inc_ref(v_value_1802_);
v_body_1803_ = lean_ctor_get(v_target_1793_, 3);
lean_inc_ref(v_body_1803_);
lean_dec_ref(v_target_1793_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed), 15, 5);
lean_closure_set(v___f_1804_, 0, v_body_1803_);
lean_closure_set(v___f_1804_, 1, v_u_1790_);
lean_closure_set(v___f_1804_, 2, v_00_u03c3s_1791_);
lean_closure_set(v___f_1804_, 3, v_hyps_1792_);
lean_closure_set(v___f_1804_, 4, v_k_1780_);
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1779_);
v___x_1818_ = l_Lean_Syntax_isOfKind(v_ident_1779_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_dec(v_ident_1779_);
v___x_1819_ = l_Lean_Core_mkFreshUserName(v_declName_1800_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v_name_1806_ = v_a_1820_;
v___y_1807_ = v___y_1781_;
v___y_1808_ = v___y_1782_;
v___y_1809_ = v___y_1783_;
v___y_1810_ = v___y_1784_;
v___y_1811_ = v___y_1785_;
v___y_1812_ = v___y_1786_;
v___y_1813_ = v___y_1787_;
v___y_1814_ = v___y_1788_;
goto v___jp_1805_;
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec_ref(v___f_1804_);
lean_dec_ref(v_value_1802_);
lean_dec_ref(v_type_1801_);
v_a_1821_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1819_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1819_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v___x_1829_; lean_object* v_name_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1829_ = lean_unsigned_to_nat(0u);
v_name_1830_ = l_Lean_Syntax_getArg(v_ident_1779_, v___x_1829_);
lean_dec(v_ident_1779_);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_1830_);
v___x_1832_ = l_Lean_Syntax_isOfKind(v_name_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; 
lean_dec(v_name_1830_);
v___x_1833_ = l_Lean_Core_mkFreshUserName(v_declName_1800_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v_name_1806_ = v_a_1834_;
v___y_1807_ = v___y_1781_;
v___y_1808_ = v___y_1782_;
v___y_1809_ = v___y_1783_;
v___y_1810_ = v___y_1784_;
v___y_1811_ = v___y_1785_;
v___y_1812_ = v___y_1786_;
v___y_1813_ = v___y_1787_;
v___y_1814_ = v___y_1788_;
goto v___jp_1805_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v___f_1804_);
lean_dec_ref(v_value_1802_);
lean_dec_ref(v_type_1801_);
v_a_1835_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1833_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1833_);
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
lean_object* v___x_1843_; 
lean_dec(v_declName_1800_);
v___x_1843_ = l_Lean_TSyntax_getId(v_name_1830_);
lean_dec(v_name_1830_);
v_name_1806_ = v___x_1843_;
v___y_1807_ = v___y_1781_;
v___y_1808_ = v___y_1782_;
v___y_1809_ = v___y_1783_;
v___y_1810_ = v___y_1784_;
v___y_1811_ = v___y_1785_;
v___y_1812_ = v___y_1786_;
v___y_1813_ = v___y_1787_;
v___y_1814_ = v___y_1788_;
goto v___jp_1805_;
}
}
v___jp_1805_:
{
uint8_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = 0;
v___x_1816_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1806_, v_type_1801_, v_value_1802_, v___f_1804_, v___x_1799_, v___x_1815_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1816_;
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref(v_hyps_1792_);
lean_dec_ref(v_00_u03c3s_1791_);
lean_dec(v_u_1790_);
lean_dec_ref(v_k_1780_);
lean_dec(v_ident_1779_);
v___x_1844_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_1845_ = l_Lean_MessageData_ofExpr(v_target_1793_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1846_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
return v___x_1847_;
}
}
else
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_1779_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1852_; lean_object* v_a_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_hyp_1858_; lean_object* v___x_1859_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
v_fst_1850_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_fst_1850_);
v_snd_1851_ = lean_ctor_get(v_a_1849_, 1);
lean_inc(v_snd_1851_);
lean_dec(v_a_1849_);
v___x_1852_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1788_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = l_Lean_Expr_appFn_x21(v_target_1793_);
v___x_1855_ = l_Lean_Expr_appFn_x21(v___x_1854_);
v___x_1856_ = l_Lean_Expr_appArg_x21(v___x_1855_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = l_Lean_Expr_appArg_x21(v___x_1854_);
lean_dec_ref(v___x_1854_);
v_hyp_1858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_1858_, 0, v_fst_1850_);
lean_ctor_set(v_hyp_1858_, 1, v_a_1853_);
lean_ctor_set(v_hyp_1858_, 2, v___x_1857_);
lean_inc_ref(v_hyp_1858_);
lean_inc_ref(v___x_1856_);
v___x_1859_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1851_, v___x_1856_, v_hyp_1858_, v___x_1799_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_H_1860_; lean_object* v___x_1861_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v___x_1859_);
v_H_1860_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_1858_);
lean_inc_ref(v_H_1860_);
lean_inc_ref(v_hyps_1792_);
lean_inc_ref(v_00_u03c3s_1791_);
lean_inc(v_u_1790_);
v___x_1861_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_1790_, v_00_u03c3s_1791_, v_hyps_1792_, v_H_1860_);
v_fst_1862_ = lean_ctor_get(v___x_1861_, 0);
v_snd_1863_ = lean_ctor_get(v___x_1861_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1865_ = v___x_1861_;
v_isShared_1866_ = v_isSharedCheck_1887_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snd_1863_);
lean_inc(v_fst_1862_);
lean_dec(v___x_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1887_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = l_Lean_Expr_appArg_x21(v_target_1793_);
lean_dec_ref(v_target_1793_);
lean_inc_ref(v___x_1867_);
lean_inc(v_fst_1862_);
lean_inc(v_u_1790_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 3, v___x_1867_);
lean_ctor_set(v___x_1795_, 2, v_fst_1862_);
v___x_1869_ = v___x_1795_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_u_1790_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_00_u03c3s_1791_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_fst_1862_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
lean_inc(v___y_1788_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
v___x_1870_ = lean_apply_10(v_k_1780_, v___x_1869_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, lean_box(0));
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1885_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1885_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1885_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0));
v___x_1876_ = lean_box(0);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 1);
lean_ctor_set(v___x_1865_, 1, v___x_1876_);
lean_ctor_set(v___x_1865_, 0, v_u_1790_);
v___x_1878_ = v___x_1865_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_u_1790_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v_prf_1880_; lean_object* v___x_1882_; 
v___x_1879_ = l_Lean_mkConst(v___x_1875_, v___x_1878_);
v_prf_1880_ = l_Lean_mkApp7(v___x_1879_, v___x_1856_, v_fst_1862_, v_hyps_1792_, v_H_1860_, v___x_1867_, v_snd_1863_, v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_prf_1880_);
v___x_1882_ = v___x_1873_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_prf_1880_);
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
else
{
lean_dec_ref(v___x_1867_);
lean_del_object(v___x_1865_);
lean_dec(v_snd_1863_);
lean_dec(v_fst_1862_);
lean_dec_ref(v_H_1860_);
lean_dec_ref(v___x_1856_);
lean_dec_ref(v_hyps_1792_);
lean_dec(v_u_1790_);
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_hyp_1858_);
lean_dec_ref(v___x_1856_);
lean_del_object(v___x_1795_);
lean_dec_ref(v_target_1793_);
lean_dec_ref(v_hyps_1792_);
lean_dec_ref(v_00_u03c3s_1791_);
lean_dec(v_u_1790_);
lean_dec_ref(v_k_1780_);
v_a_1888_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1859_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1859_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_del_object(v___x_1795_);
lean_dec_ref(v_target_1793_);
lean_dec_ref(v_hyps_1792_);
lean_dec_ref(v_00_u03c3s_1791_);
lean_dec(v_u_1790_);
lean_dec_ref(v_k_1780_);
v_a_1896_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1848_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1848_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(lean_object* v_goal_1905_, lean_object* v_ident_1906_, lean_object* v_k_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_1905_, v_ident_1906_, v_k_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(lean_object* v___x_1918_, lean_object* v_snd_1919_, lean_object* v_ident_1920_, lean_object* v_fst_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_st_mk_ref(v___x_1918_);
lean_inc(v___x_1931_);
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1932_, 0, v___x_1931_);
v___x_1933_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_snd_1919_, v_ident_1920_, v___f_1932_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1921_, v_a_1934_, v___y_1927_);
lean_dec_ref(v___x_1935_);
v___x_1936_ = lean_st_ref_get(v___x_1931_);
lean_dec(v___x_1931_);
v___x_1937_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1936_, v___y_1923_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v___x_1937_;
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v___x_1931_);
lean_dec(v_fst_1921_);
v_a_1938_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1933_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1933_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed(lean_object* v___x_1946_, lean_object* v_snd_1947_, lean_object* v_ident_1948_, lean_object* v_fst_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(v___x_1946_, v_snd_1947_, v_ident_1948_, v_fst_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(lean_object* v_x_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_1966_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v_x_1966_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_x_1966_);
v___x_1978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = l_Lean_Syntax_getArg(v_x_1966_, v___x_1979_);
lean_dec(v_x_1966_);
lean_inc(v___x_1980_);
v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1980_, v___x_1979_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec(v___x_1980_);
v___x_1982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = l_Lean_Syntax_getArg(v___x_1980_, v___x_1983_);
lean_dec(v___x_1980_);
v___x_1985_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_1984_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1));
lean_inc(v___x_1984_);
v___x_1988_ = l_Lean_Syntax_isOfKind(v___x_1984_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec(v___x_1984_);
v___x_1989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1989_;
}
else
{
lean_object* v_ident_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v_ident_1990_ = l_Lean_Syntax_getArg(v___x_1984_, v___x_1979_);
lean_dec(v___x_1984_);
v___x_1991_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1990_);
v___x_1992_ = l_Lean_Syntax_isOfKind(v_ident_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
lean_dec(v_ident_1990_);
v___x_1993_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1993_;
}
else
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1968_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___x_2000_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
v_fst_1996_ = lean_ctor_get(v_a_1995_, 0);
lean_inc_n(v_fst_1996_, 2);
v_snd_1997_ = lean_ctor_get(v_a_1995_, 1);
lean_inc(v_snd_1997_);
lean_dec(v_a_1995_);
v___x_1998_ = lean_box(0);
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1999_, 0, v___x_1998_);
lean_closure_set(v___f_1999_, 1, v_snd_1997_);
lean_closure_set(v___f_1999_, 2, v_ident_1990_);
lean_closure_set(v___f_1999_, 3, v_fst_1996_);
v___x_2000_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_1996_, v___f_1999_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_2000_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_ident_1990_);
v_a_2001_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1994_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1994_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = l_Lean_Syntax_getArg(v___x_1984_, v___x_1983_);
lean_dec(v___x_1984_);
v___x_2010_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_2009_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec(v___x_2009_);
v___x_2012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2012_;
}
else
{
lean_object* v_ident_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_ident_2013_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_1983_);
lean_dec(v___x_2009_);
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_2013_);
v___x_2015_ = l_Lean_Syntax_isOfKind(v_ident_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec(v_ident_2013_);
v___x_2016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1968_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v_fst_2019_; lean_object* v_snd_2020_; lean_object* v___x_2021_; lean_object* v___f_2022_; lean_object* v___x_2023_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___x_2017_);
v_fst_2019_ = lean_ctor_get(v_a_2018_, 0);
lean_inc_n(v_fst_2019_, 2);
v_snd_2020_ = lean_ctor_get(v_a_2018_, 1);
lean_inc(v_snd_2020_);
lean_dec(v_a_2018_);
v___x_2021_ = lean_box(0);
v___f_2022_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2022_, 0, v___x_2021_);
lean_closure_set(v___f_2022_, 1, v_snd_2020_);
lean_closure_set(v___f_2022_, 2, v_ident_2013_);
lean_closure_set(v___f_2022_, 3, v_fst_2019_);
v___x_2023_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2019_, v___f_2022_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_2023_;
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_ident_2013_);
v_a_2024_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2017_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2017_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(lean_object* v_x_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(v_x_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(lean_object* v_mvarId_2043_, lean_object* v_val_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_2043_, v_val_2044_, v___y_2050_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(lean_object* v_mvarId_2055_, lean_object* v_val_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(v_mvarId_2055_, v_val_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_object* v_00_u03b1_2067_, lean_object* v_name_2068_, lean_object* v_type_2069_, lean_object* v_val_2070_, lean_object* v_k_2071_, uint8_t v_nondep_2072_, uint8_t v_kind_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_2068_, v_type_2069_, v_val_2070_, v_k_2071_, v_nondep_2072_, v_kind_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_name_2085_, lean_object* v_type_2086_, lean_object* v_val_2087_, lean_object* v_k_2088_, lean_object* v_nondep_2089_, lean_object* v_kind_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v_nondep_boxed_2100_; uint8_t v_kind_boxed_2101_; lean_object* v_res_2102_; 
v_nondep_boxed_2100_ = lean_unbox(v_nondep_2089_);
v_kind_boxed_2101_ = lean_unbox(v_kind_2090_);
v_res_2102_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(v_00_u03b1_2084_, v_name_2085_, v_type_2086_, v_val_2087_, v_k_2088_, v_nondep_boxed_2100_, v_kind_boxed_2101_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_object* v_00_u03b1_2115_, lean_object* v_msg_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(v_00_u03b1_2123_, v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2131_, lean_object* v_name_2132_, uint8_t v_bi_2133_, lean_object* v_type_2134_, lean_object* v_k_2135_, uint8_t v_kind_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_2132_, v_bi_2133_, v_type_2134_, v_k_2135_, v_kind_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_name_2144_, lean_object* v_bi_2145_, lean_object* v_type_2146_, lean_object* v_k_2147_, lean_object* v_kind_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v_bi_boxed_2154_; uint8_t v_kind_boxed_2155_; lean_object* v_res_2156_; 
v_bi_boxed_2154_ = lean_unbox(v_bi_2145_);
v_kind_boxed_2155_ = lean_unbox(v_kind_2148_);
v_res_2156_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(v_00_u03b1_2143_, v_name_2144_, v_bi_boxed_2154_, v_type_2146_, v_k_2147_, v_kind_boxed_2155_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_object* v_00_u03b1_2157_, lean_object* v_name_2158_, lean_object* v_type_2159_, lean_object* v_k_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_2158_, v_type_2159_, v_k_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_name_2168_, lean_object* v_type_2169_, lean_object* v_k_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(v_00_u03b1_2167_, v_name_2168_, v_type_2169_, v_k_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(lean_object* v_00_u03b2_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_x_2178_, v_x_2179_, v_x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2182_, lean_object* v_x_2183_, size_t v_x_2184_, size_t v_x_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_2183_, v_x_2184_, v_x_2185_, v_x_2186_, v_x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
size_t v_x_21863__boxed_2195_; size_t v_x_21864__boxed_2196_; lean_object* v_res_2197_; 
v_x_21863__boxed_2195_ = lean_unbox_usize(v_x_2191_);
lean_dec(v_x_2191_);
v_x_21864__boxed_2196_ = lean_unbox_usize(v_x_2192_);
lean_dec(v_x_2192_);
v_res_2197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(v_00_u03b2_2189_, v_x_2190_, v_x_21863__boxed_2195_, v_x_21864__boxed_2196_, v_x_2193_, v_x_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2198_, lean_object* v_n_2199_, lean_object* v_k_2200_, lean_object* v_v_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v_n_2199_, v_k_2200_, v_v_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b2_2203_, size_t v_depth_2204_, lean_object* v_keys_2205_, lean_object* v_vals_2206_, lean_object* v_heq_2207_, lean_object* v_i_2208_, lean_object* v_entries_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_2204_, v_keys_2205_, v_vals_2206_, v_i_2208_, v_entries_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b2_2211_, lean_object* v_depth_2212_, lean_object* v_keys_2213_, lean_object* v_vals_2214_, lean_object* v_heq_2215_, lean_object* v_i_2216_, lean_object* v_entries_2217_){
_start:
{
size_t v_depth_boxed_2218_; lean_object* v_res_2219_; 
v_depth_boxed_2218_ = lean_unbox_usize(v_depth_2212_);
lean_dec(v_depth_2212_);
v_res_2219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(v_00_u03b2_2211_, v_depth_boxed_2218_, v_keys_2213_, v_vals_2214_, v_heq_2215_, v_i_2216_, v_entries_2217_);
lean_dec_ref(v_vals_2214_);
lean_dec_ref(v_keys_2213_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_x_2221_, v_x_2222_, v_x_2223_, v_x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1(){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2237_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_2239_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3));
v___x_2240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed), 10, 0);
v___x_2241_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2237_, v___x_2238_, v___x_2239_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
return v_res_2243_;
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
