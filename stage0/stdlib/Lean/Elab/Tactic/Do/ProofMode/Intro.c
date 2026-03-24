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
lean_object* v___x_280_; lean_object* v_toApplicative_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_406_; 
v___x_280_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_280_, 1);
lean_dec(v_unused_407_);
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_406_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_toApplicative_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_406_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_toFunctor_285_; lean_object* v_toSeq_286_; lean_object* v_toSeqLeft_287_; lean_object* v_toSeqRight_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_404_; 
v_toFunctor_285_ = lean_ctor_get(v_toApplicative_281_, 0);
v_toSeq_286_ = lean_ctor_get(v_toApplicative_281_, 2);
v_toSeqLeft_287_ = lean_ctor_get(v_toApplicative_281_, 3);
v_toSeqRight_288_ = lean_ctor_get(v_toApplicative_281_, 4);
v_isSharedCheck_404_ = !lean_is_exclusive(v_toApplicative_281_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v_toApplicative_281_, 1);
lean_dec(v_unused_405_);
v___x_290_ = v_toApplicative_281_;
v_isShared_291_ = v_isSharedCheck_404_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_toSeqRight_288_);
lean_inc(v_toSeqLeft_287_);
lean_inc(v_toSeq_286_);
lean_inc(v_toFunctor_285_);
lean_dec(v_toApplicative_281_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_404_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___f_292_; lean_object* v___f_293_; lean_object* v___f_294_; lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___x_301_; 
v___f_292_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_293_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref(v_toFunctor_285_);
v___f_294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_294_, 0, v_toFunctor_285_);
v___f_295_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_295_, 0, v_toFunctor_285_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___f_294_);
lean_ctor_set(v___x_296_, 1, v___f_295_);
v___f_297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_297_, 0, v_toSeqRight_288_);
v___f_298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_298_, 0, v_toSeqLeft_287_);
v___f_299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_299_, 0, v_toSeq_286_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___f_297_);
lean_ctor_set(v___x_290_, 3, v___f_298_);
lean_ctor_set(v___x_290_, 2, v___f_299_);
lean_ctor_set(v___x_290_, 1, v___f_292_);
lean_ctor_set(v___x_290_, 0, v___x_296_);
v___x_301_ = v___x_290_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___f_292_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v___f_299_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v___f_298_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v___f_297_);
v___x_301_ = v_reuseFailAlloc_403_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___f_293_);
lean_ctor_set(v___x_283_, 0, v___x_301_);
v___x_303_ = v___x_283_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___f_293_);
v___x_303_ = v_reuseFailAlloc_402_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v_toApplicative_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_400_; 
v___x_304_ = l_StateRefT_x27_instMonad___redArg(v___x_303_);
v_toApplicative_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v___x_304_, 1);
lean_dec(v_unused_401_);
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_400_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_toApplicative_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_400_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_toFunctor_309_; lean_object* v_toSeq_310_; lean_object* v_toSeqLeft_311_; lean_object* v_toSeqRight_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_398_; 
v_toFunctor_309_ = lean_ctor_get(v_toApplicative_305_, 0);
v_toSeq_310_ = lean_ctor_get(v_toApplicative_305_, 2);
v_toSeqLeft_311_ = lean_ctor_get(v_toApplicative_305_, 3);
v_toSeqRight_312_ = lean_ctor_get(v_toApplicative_305_, 4);
v_isSharedCheck_398_ = !lean_is_exclusive(v_toApplicative_305_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v_toApplicative_305_, 1);
lean_dec(v_unused_399_);
v___x_314_ = v_toApplicative_305_;
v_isShared_315_ = v_isSharedCheck_398_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_toSeqRight_312_);
lean_inc(v_toSeqLeft_311_);
lean_inc(v_toSeq_310_);
lean_inc(v_toFunctor_309_);
lean_dec(v_toApplicative_305_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_398_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___x_325_; 
v___f_316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_317_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_309_);
v___f_318_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_318_, 0, v_toFunctor_309_);
v___f_319_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_319_, 0, v_toFunctor_309_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___f_318_);
lean_ctor_set(v___x_320_, 1, v___f_319_);
v___f_321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_321_, 0, v_toSeqRight_312_);
v___f_322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_322_, 0, v_toSeqLeft_311_);
v___f_323_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_323_, 0, v_toSeq_310_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___f_321_);
lean_ctor_set(v___x_314_, 3, v___f_322_);
lean_ctor_set(v___x_314_, 2, v___f_323_);
lean_ctor_set(v___x_314_, 1, v___f_316_);
lean_ctor_set(v___x_314_, 0, v___x_320_);
v___x_325_ = v___x_314_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___f_316_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v___f_323_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v___f_322_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v___f_321_);
v___x_325_ = v_reuseFailAlloc_397_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___f_317_);
lean_ctor_set(v___x_307_, 0, v___x_325_);
v___x_327_ = v___x_307_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___f_317_);
v___x_327_ = v_reuseFailAlloc_396_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_toMonadRef_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_toApplicative_335_; lean_object* v_toBind_336_; lean_object* v_toPure_337_; lean_object* v_u_338_; lean_object* v_00_u03c3s_339_; lean_object* v_hyps_340_; lean_object* v_target_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_328_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9);
v___x_329_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_330_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19);
v_toMonadRef_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_toMonadRef_331_);
v___x_332_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_327_);
v___x_333_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_332_, v___x_327_);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v___x_329_);
lean_ctor_set(v___x_334_, 1, v_toMonadRef_331_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v_toApplicative_335_ = lean_ctor_get(v_inst_274_, 0);
v_toBind_336_ = lean_ctor_get(v_inst_274_, 1);
v_toPure_337_ = lean_ctor_get(v_toApplicative_335_, 1);
v_u_338_ = lean_ctor_get(v_goal_277_, 0);
lean_inc(v_u_338_);
v_00_u03c3s_339_ = lean_ctor_get(v_goal_277_, 1);
lean_inc_ref(v_00_u03c3s_339_);
v_hyps_340_ = lean_ctor_get(v_goal_277_, 2);
lean_inc_ref(v_hyps_340_);
v_target_341_ = lean_ctor_get(v_goal_277_, 3);
lean_inc_ref(v_target_341_);
lean_dec_ref(v_goal_277_);
v___x_342_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20));
v___x_343_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21));
v___x_344_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22));
v___x_345_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_346_ = lean_unsigned_to_nat(3u);
v___x_347_ = l_Lean_Expr_isAppOfArity(v_target_341_, v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
if (lean_obj_tag(v_target_341_) == 8)
{
lean_object* v_declName_348_; lean_object* v_type_349_; lean_object* v_value_350_; lean_object* v_body_351_; lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
lean_inc(v_toPure_337_);
lean_inc(v_toBind_336_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_327_);
v_declName_348_ = lean_ctor_get(v_target_341_, 0);
lean_inc(v_declName_348_);
v_type_349_ = lean_ctor_get(v_target_341_, 1);
lean_inc_ref(v_type_349_);
v_value_350_ = lean_ctor_get(v_target_341_, 2);
lean_inc_ref(v_value_350_);
v_body_351_ = lean_ctor_get(v_target_341_, 3);
lean_inc_ref(v_body_351_);
lean_dec_ref(v_target_341_);
lean_inc(v_toBind_336_);
lean_inc(v_inst_276_);
v___f_352_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_352_, 0, v_inst_276_);
lean_closure_set(v___f_352_, 1, v_body_351_);
lean_closure_set(v___f_352_, 2, v_u_338_);
lean_closure_set(v___f_352_, 3, v_00_u03c3s_339_);
lean_closure_set(v___f_352_, 4, v_hyps_340_);
lean_closure_set(v___f_352_, 5, v_k_279_);
lean_closure_set(v___f_352_, 6, v_toBind_336_);
v___x_353_ = lean_box(v___x_347_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_354_, 0, v_inst_275_);
lean_closure_set(v___f_354_, 1, v_inst_274_);
lean_closure_set(v___f_354_, 2, v_type_349_);
lean_closure_set(v___f_354_, 3, v_value_350_);
lean_closure_set(v___f_354_, 4, v___f_352_);
lean_closure_set(v___f_354_, 5, v___x_353_);
v___x_355_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_278_);
v___x_356_ = l_Lean_Syntax_isOfKind(v_ident_278_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___f_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v_toPure_337_);
lean_dec(v_ident_278_);
v___f_357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_357_, 0, v___f_354_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_358_, 0, v_declName_348_);
v___x_359_ = lean_apply_2(v_inst_276_, lean_box(0), v___f_358_);
v___x_360_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v___x_359_, v___f_357_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; lean_object* v_name_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v_name_362_ = l_Lean_Syntax_getArg(v_ident_278_, v___x_361_);
lean_dec(v_ident_278_);
v___x_363_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_362_);
v___x_364_ = l_Lean_Syntax_isOfKind(v_name_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v_name_362_);
lean_dec(v_toPure_337_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_365_, 0, v___f_354_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_366_, 0, v_declName_348_);
v___x_367_ = lean_apply_2(v_inst_276_, lean_box(0), v___f_366_);
v___x_368_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v___x_367_, v___f_365_);
return v___x_368_;
}
else
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_declName_348_);
lean_dec(v_inst_276_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_369_, 0, v___f_354_);
v___x_370_ = l_Lean_TSyntax_getId(v_name_362_);
lean_dec(v_name_362_);
v___x_371_ = lean_apply_2(v_toPure_337_, lean_box(0), v___x_370_);
v___x_372_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v___x_371_, v___f_369_);
return v___x_372_;
}
}
}
else
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_hyps_340_);
lean_dec_ref(v_00_u03c3s_339_);
lean_dec(v_u_338_);
lean_dec(v_k_279_);
lean_dec(v_ident_278_);
lean_dec_ref(v_inst_275_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_inst_274_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_inst_274_, 1);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_inst_274_, 0);
lean_dec(v_unused_385_);
v___x_374_ = v_inst_274_;
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_inst_274_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_377_ = l_Lean_MessageData_ofExpr(v_target_341_);
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 7);
lean_ctor_set(v___x_374_, 1, v___x_377_);
lean_ctor_set(v___x_374_, 0, v___x_376_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_377_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = l_Lean_throwError___redArg(v___x_327_, v___x_334_, v___x_379_);
v___x_381_ = lean_apply_2(v_inst_276_, lean_box(0), v___x_380_);
return v___x_381_;
}
}
}
}
else
{
lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc(v_toPure_337_);
lean_inc(v_toBind_336_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_274_);
v___f_386_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed), 6, 1);
lean_closure_set(v___f_386_, 0, v_ident_278_);
v___x_387_ = l_Lean_Expr_appFn_x21(v_target_341_);
v___x_388_ = l_Lean_Expr_appFn_x21(v___x_387_);
v___x_389_ = l_Lean_Expr_appArg_x21(v___x_388_);
lean_dec_ref(v___x_388_);
v___x_390_ = l_Lean_Expr_appArg_x21(v___x_387_);
lean_dec_ref(v___x_387_);
v___x_391_ = l_Lean_Expr_appArg_x21(v_target_341_);
lean_dec_ref(v_target_341_);
v___x_392_ = lean_box(v___x_347_);
lean_inc(v_inst_276_);
lean_inc(v_toBind_336_);
v___f_393_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_393_, 0, v___x_390_);
lean_closure_set(v___f_393_, 1, v_u_338_);
lean_closure_set(v___f_393_, 2, v_00_u03c3s_339_);
lean_closure_set(v___f_393_, 3, v_hyps_340_);
lean_closure_set(v___f_393_, 4, v___x_342_);
lean_closure_set(v___f_393_, 5, v___x_343_);
lean_closure_set(v___f_393_, 6, v___x_344_);
lean_closure_set(v___f_393_, 7, v___x_389_);
lean_closure_set(v___f_393_, 8, v___x_391_);
lean_closure_set(v___f_393_, 9, v_toPure_337_);
lean_closure_set(v___f_393_, 10, v_k_279_);
lean_closure_set(v___f_393_, 11, v_toBind_336_);
lean_closure_set(v___f_393_, 12, v___x_392_);
lean_closure_set(v___f_393_, 13, v_inst_276_);
lean_closure_set(v___f_393_, 14, v___x_327_);
lean_closure_set(v___f_393_, 15, v___x_328_);
v___x_394_ = lean_apply_2(v_inst_276_, lean_box(0), v___f_386_);
v___x_395_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v___x_394_, v___f_393_);
return v___x_395_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro(lean_object* v_m_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_goal_412_, lean_object* v_ident_413_, lean_object* v_k_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_goal_412_, v_ident_413_, v_k_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0(lean_object* v_u_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v_hyps_425_, lean_object* v_target_426_, lean_object* v_toPure_427_, lean_object* v_prf_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v_u_422_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_mkConst(v___x_429_, v___x_431_);
v___x_433_ = l_Lean_mkApp5(v___x_432_, v___x_423_, v___x_424_, v_hyps_425_, v_target_426_, v_prf_428_);
v___x_434_ = lean_apply_2(v_toPure_427_, lean_box(0), v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(lean_object* v___x_435_, uint8_t v___x_436_, uint8_t v___x_437_, lean_object* v_inst_438_, lean_object* v_toBind_439_, lean_object* v___f_440_, lean_object* v_prf_441_){
_start:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_442_ = 1;
v___x_443_ = lean_box(v___x_436_);
v___x_444_ = lean_box(v___x_437_);
v___x_445_ = lean_box(v___x_436_);
v___x_446_ = lean_box(v___x_437_);
v___x_447_ = lean_box(v___x_442_);
v___x_448_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_448_, 0, v___x_435_);
lean_closure_set(v___x_448_, 1, v_prf_441_);
lean_closure_set(v___x_448_, 2, v___x_443_);
lean_closure_set(v___x_448_, 3, v___x_444_);
lean_closure_set(v___x_448_, 4, v___x_445_);
lean_closure_set(v___x_448_, 5, v___x_446_);
lean_closure_set(v___x_448_, 6, v___x_447_);
v___x_449_ = lean_apply_2(v_inst_438_, lean_box(0), v___x_448_);
v___x_450_ = lean_apply_4(v_toBind_439_, lean_box(0), lean_box(0), v___x_449_, v___f_440_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed(lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v_inst_454_, lean_object* v_toBind_455_, lean_object* v___f_456_, lean_object* v_prf_457_){
_start:
{
uint8_t v___x_2265__boxed_458_; uint8_t v___x_2266__boxed_459_; lean_object* v_res_460_; 
v___x_2265__boxed_458_ = lean_unbox(v___x_452_);
v___x_2266__boxed_459_ = lean_unbox(v___x_453_);
v_res_460_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(v___x_451_, v___x_2265__boxed_458_, v___x_2266__boxed_459_, v_inst_454_, v_toBind_455_, v___f_456_, v_prf_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(lean_object* v___x_461_, lean_object* v_ident_462_, uint8_t v___x_463_, lean_object* v_hyps_464_, lean_object* v___x_465_, lean_object* v_inst_466_, lean_object* v_toBind_467_, lean_object* v___f_468_, lean_object* v_target_469_, lean_object* v_u_470_, lean_object* v_k_471_, lean_object* v_map_472_, lean_object* v_s_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_lctx_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_lctx_479_ = lean_ctor_get(v___y_474_, 2);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_461_);
lean_inc_ref(v_s_473_);
lean_inc_ref(v_lctx_479_);
v___x_481_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_462_, v_lctx_479_, v_s_473_, v___x_480_, v___x_463_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref(v___x_481_);
lean_inc_ref(v_s_473_);
v___x_482_ = l_Lean_Expr_app___override(v_hyps_464_, v_s_473_);
lean_inc_ref(v___x_465_);
v___x_483_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_465_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
v___x_486_ = lean_array_push(v___x_485_, v_s_473_);
v___x_487_ = 0;
v___x_488_ = lean_box(v___x_487_);
v___x_489_ = lean_box(v___x_463_);
lean_inc(v_toBind_467_);
lean_inc_ref(v___x_486_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_490_, 0, v___x_486_);
lean_closure_set(v___f_490_, 1, v___x_488_);
lean_closure_set(v___f_490_, 2, v___x_489_);
lean_closure_set(v___f_490_, 3, v_inst_466_);
lean_closure_set(v___f_490_, 4, v_toBind_467_);
lean_closure_set(v___f_490_, 5, v___f_468_);
v___x_491_ = l_Lean_Expr_betaRev(v_target_469_, v___x_486_, v___x_487_, v___x_487_);
lean_dec_ref(v___x_486_);
v___x_492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_492_, 0, v_u_470_);
lean_ctor_set(v___x_492_, 1, v___x_465_);
lean_ctor_set(v___x_492_, 2, v___x_483_);
lean_ctor_set(v___x_492_, 3, v___x_491_);
v___x_493_ = lean_apply_1(v_k_471_, v___x_492_);
v___x_494_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_493_, v___f_490_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
v___x_495_ = lean_apply_7(v_map_472_, lean_box(0), v___x_494_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, lean_box(0));
return v___x_495_;
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___y_474_);
lean_dec_ref(v_s_473_);
lean_dec_ref(v_map_472_);
lean_dec(v_k_471_);
lean_dec(v_u_470_);
lean_dec_ref(v_target_469_);
lean_dec(v___f_468_);
lean_dec(v_toBind_467_);
lean_dec(v_inst_466_);
lean_dec_ref(v___x_465_);
lean_dec_ref(v_hyps_464_);
v_a_496_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_481_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_481_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_504_ = _args[0];
lean_object* v_ident_505_ = _args[1];
lean_object* v___x_506_ = _args[2];
lean_object* v_hyps_507_ = _args[3];
lean_object* v___x_508_ = _args[4];
lean_object* v_inst_509_ = _args[5];
lean_object* v_toBind_510_ = _args[6];
lean_object* v___f_511_ = _args[7];
lean_object* v_target_512_ = _args[8];
lean_object* v_u_513_ = _args[9];
lean_object* v_k_514_ = _args[10];
lean_object* v_map_515_ = _args[11];
lean_object* v_s_516_ = _args[12];
lean_object* v___y_517_ = _args[13];
lean_object* v___y_518_ = _args[14];
lean_object* v___y_519_ = _args[15];
lean_object* v___y_520_ = _args[16];
lean_object* v___y_521_ = _args[17];
_start:
{
uint8_t v___x_2298__boxed_522_; lean_object* v_res_523_; 
v___x_2298__boxed_522_ = lean_unbox(v___x_506_);
v_res_523_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(v___x_504_, v_ident_505_, v___x_2298__boxed_522_, v_hyps_507_, v___x_508_, v_inst_509_, v_toBind_510_, v___f_511_, v_target_512_, v_u_513_, v_k_514_, v_map_515_, v_s_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
return v_res_523_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(lean_object* v_goal_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_toPure_538_, lean_object* v_ident_539_, lean_object* v_inst_540_, lean_object* v_toBind_541_, lean_object* v_k_542_, lean_object* v___x_543_, lean_object* v_map_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_u_550_; lean_object* v_00_u03c3s_551_; lean_object* v_hyps_552_; lean_object* v_target_553_; lean_object* v___x_554_; 
v_u_550_ = lean_ctor_get(v_goal_535_, 0);
lean_inc(v_u_550_);
v_00_u03c3s_551_ = lean_ctor_get(v_goal_535_, 1);
lean_inc_ref(v_00_u03c3s_551_);
v_hyps_552_ = lean_ctor_get(v_goal_535_, 2);
lean_inc_ref(v_hyps_552_);
v_target_553_ = lean_ctor_get(v_goal_535_, 3);
lean_inc_ref(v_target_553_);
lean_dec_ref(v_goal_535_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v_00_u03c3s_551_);
v___x_554_ = lean_whnf(v_00_u03c3s_551_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref(v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_557_ = lean_unsigned_to_nat(3u);
v___x_558_ = l_Lean_Expr_isAppOfArity(v_a_555_, v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_2189__overap_562_; lean_object* v___x_563_; 
lean_dec(v_a_555_);
lean_dec_ref(v_target_553_);
lean_dec_ref(v_hyps_552_);
lean_dec(v_u_550_);
lean_dec_ref(v_map_544_);
lean_dec_ref(v___x_543_);
lean_dec(v_k_542_);
lean_dec(v_toBind_541_);
lean_dec(v_inst_540_);
lean_dec(v_ident_539_);
lean_dec(v_toPure_538_);
v___x_559_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_560_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_551_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_2189__overap_562_ = l_Lean_throwError___redArg(v___x_536_, v___x_537_, v___x_561_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
v___x_563_ = lean_apply_5(v___x_2189__overap_562_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, lean_box(0));
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___f_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
lean_dec_ref(v_00_u03c3s_551_);
lean_dec_ref(v___x_537_);
v___x_564_ = l_Lean_Expr_appFn_x21(v_a_555_);
v___x_565_ = l_Lean_Expr_appArg_x21(v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_Lean_Expr_appArg_x21(v_a_555_);
lean_dec(v_a_555_);
lean_inc_ref(v_target_553_);
lean_inc_ref(v_hyps_552_);
lean_inc_ref(v___x_565_);
lean_inc_ref(v___x_566_);
lean_inc(v_u_550_);
v___f_567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0), 7, 6);
lean_closure_set(v___f_567_, 0, v_u_550_);
lean_closure_set(v___f_567_, 1, v___x_566_);
lean_closure_set(v___f_567_, 2, v___x_565_);
lean_closure_set(v___f_567_, 3, v_hyps_552_);
lean_closure_set(v___f_567_, 4, v_target_553_);
lean_closure_set(v___f_567_, 5, v_toPure_538_);
v___x_568_ = lean_box(v___x_558_);
lean_inc(v_ident_539_);
lean_inc_ref(v___x_565_);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed), 18, 12);
lean_closure_set(v___f_569_, 0, v___x_565_);
lean_closure_set(v___f_569_, 1, v_ident_539_);
lean_closure_set(v___f_569_, 2, v___x_568_);
lean_closure_set(v___f_569_, 3, v_hyps_552_);
lean_closure_set(v___f_569_, 4, v___x_566_);
lean_closure_set(v___f_569_, 5, v_inst_540_);
lean_closure_set(v___f_569_, 6, v_toBind_541_);
lean_closure_set(v___f_569_, 7, v___f_567_);
lean_closure_set(v___f_569_, 8, v_target_553_);
lean_closure_set(v___f_569_, 9, v_u_550_);
lean_closure_set(v___f_569_, 10, v_k_542_);
lean_closure_set(v___f_569_, 11, v_map_544_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_539_);
v___x_571_ = l_Lean_Syntax_isOfKind(v_ident_539_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_ident_539_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_573_ = l_Lean_Core_mkFreshUserName(v___x_572_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_2204__overap_575_; lean_object* v___x_576_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_573_);
v___x_2204__overap_575_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_543_, v___x_536_, v_a_574_, v___x_565_, v___f_569_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
v___x_576_ = lean_apply_5(v___x_2204__overap_575_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, lean_box(0));
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v___f_569_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_536_);
v_a_577_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_573_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_573_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = l_Lean_Syntax_getArg(v_ident_539_, v___x_585_);
lean_dec(v_ident_539_);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_586_);
v___x_588_ = l_Lean_Syntax_isOfKind(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v___x_586_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_590_ = l_Lean_Core_mkFreshUserName(v___x_589_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_2218__overap_592_; lean_object* v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_590_);
v___x_2218__overap_592_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_543_, v___x_536_, v_a_591_, v___x_565_, v___f_569_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
v___x_593_ = lean_apply_5(v___x_2218__overap_592_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, lean_box(0));
return v___x_593_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v___f_569_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_536_);
v_a_594_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_590_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_2223__overap_603_; lean_object* v___x_604_; 
v___x_602_ = l_Lean_TSyntax_getId(v___x_586_);
lean_dec(v___x_586_);
v___x_2223__overap_603_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_543_, v___x_536_, v___x_602_, v___x_565_, v___f_569_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
v___x_604_ = lean_apply_5(v___x_2223__overap_603_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, lean_box(0));
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_target_553_);
lean_dec_ref(v_hyps_552_);
lean_dec_ref(v_00_u03c3s_551_);
lean_dec(v_u_550_);
lean_dec_ref(v_map_544_);
lean_dec_ref(v___x_543_);
lean_dec(v_k_542_);
lean_dec(v_toBind_541_);
lean_dec(v_inst_540_);
lean_dec(v_ident_539_);
lean_dec(v_toPure_538_);
lean_dec_ref(v___x_537_);
lean_dec_ref(v___x_536_);
v_a_605_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_554_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_554_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed(lean_object* v_goal_613_, lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_toPure_616_, lean_object* v_ident_617_, lean_object* v_inst_618_, lean_object* v_toBind_619_, lean_object* v_k_620_, lean_object* v___x_621_, lean_object* v_map_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(v_goal_613_, v___x_614_, v___x_615_, v_toPure_616_, v_ident_617_, v_inst_618_, v_toBind_619_, v_k_620_, v___x_621_, v_map_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_goal_632_, lean_object* v_ident_633_, lean_object* v_k_634_){
_start:
{
lean_object* v___x_635_; lean_object* v_toApplicative_636_; lean_object* v_toFunctor_637_; lean_object* v_toSeq_638_; lean_object* v_toSeqLeft_639_; lean_object* v_toSeqRight_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_731_; 
v___x_635_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_toApplicative_636_);
v_toFunctor_637_ = lean_ctor_get(v_toApplicative_636_, 0);
v_toSeq_638_ = lean_ctor_get(v_toApplicative_636_, 2);
v_toSeqLeft_639_ = lean_ctor_get(v_toApplicative_636_, 3);
v_toSeqRight_640_ = lean_ctor_get(v_toApplicative_636_, 4);
v_isSharedCheck_731_ = !lean_is_exclusive(v_toApplicative_636_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_toApplicative_636_, 1);
lean_dec(v_unused_732_);
v___x_642_ = v_toApplicative_636_;
v_isShared_643_ = v_isSharedCheck_731_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_toSeqRight_640_);
lean_inc(v_toSeqLeft_639_);
lean_inc(v_toSeq_638_);
lean_inc(v_toFunctor_637_);
lean_dec(v_toApplicative_636_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_731_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___f_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___x_653_; 
v___f_644_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_645_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref(v_toFunctor_637_);
v___f_646_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_646_, 0, v_toFunctor_637_);
v___f_647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_647_, 0, v_toFunctor_637_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___f_646_);
lean_ctor_set(v___x_648_, 1, v___f_647_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_649_, 0, v_toSeqRight_640_);
v___f_650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_650_, 0, v_toSeqLeft_639_);
v___f_651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_651_, 0, v_toSeq_638_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 4, v___f_649_);
lean_ctor_set(v___x_642_, 3, v___f_650_);
lean_ctor_set(v___x_642_, 2, v___f_651_);
lean_ctor_set(v___x_642_, 1, v___f_644_);
lean_ctor_set(v___x_642_, 0, v___x_648_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___f_644_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v___f_651_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v___f_650_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v___f_649_);
v___x_653_ = v_reuseFailAlloc_730_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_toApplicative_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_728_; 
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___f_645_);
v___x_655_ = l_StateRefT_x27_instMonad___redArg(v___x_654_);
v_toApplicative_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_655_, 1);
lean_dec(v_unused_729_);
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_728_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_toApplicative_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_728_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_toFunctor_660_; lean_object* v_toSeq_661_; lean_object* v_toSeqLeft_662_; lean_object* v_toSeqRight_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_726_; 
v_toFunctor_660_ = lean_ctor_get(v_toApplicative_656_, 0);
v_toSeq_661_ = lean_ctor_get(v_toApplicative_656_, 2);
v_toSeqLeft_662_ = lean_ctor_get(v_toApplicative_656_, 3);
v_toSeqRight_663_ = lean_ctor_get(v_toApplicative_656_, 4);
v_isSharedCheck_726_ = !lean_is_exclusive(v_toApplicative_656_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_toApplicative_656_, 1);
lean_dec(v_unused_727_);
v___x_665_ = v_toApplicative_656_;
v_isShared_666_ = v_isSharedCheck_726_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_toSeqRight_663_);
lean_inc(v_toSeqLeft_662_);
lean_inc(v_toSeq_661_);
lean_inc(v_toFunctor_660_);
lean_dec(v_toApplicative_656_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_726_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___x_676_; 
v___f_667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_668_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_660_);
v___f_669_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_669_, 0, v_toFunctor_660_);
v___f_670_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_670_, 0, v_toFunctor_660_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___f_669_);
lean_ctor_set(v___x_671_, 1, v___f_670_);
v___f_672_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_672_, 0, v_toSeqRight_663_);
v___f_673_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_673_, 0, v_toSeqLeft_662_);
v___f_674_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_674_, 0, v_toSeq_661_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 4, v___f_672_);
lean_ctor_set(v___x_665_, 3, v___f_673_);
lean_ctor_set(v___x_665_, 2, v___f_674_);
lean_ctor_set(v___x_665_, 1, v___f_667_);
lean_ctor_set(v___x_665_, 0, v___x_671_);
v___x_676_ = v___x_665_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___f_667_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v___f_674_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v___f_673_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v___f_672_);
v___x_676_ = v_reuseFailAlloc_725_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___f_668_);
lean_ctor_set(v___x_658_, 0, v___x_676_);
v___x_678_ = v___x_658_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___f_668_);
v___x_678_ = v_reuseFailAlloc_724_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v_toApplicative_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_722_; 
v_toApplicative_679_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_635_, 1);
lean_dec(v_unused_723_);
v___x_681_ = v___x_635_;
v_isShared_682_ = v_isSharedCheck_722_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_toApplicative_679_);
lean_dec(v___x_635_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_722_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_toFunctor_683_; lean_object* v_toSeq_684_; lean_object* v_toSeqLeft_685_; lean_object* v_toSeqRight_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_720_; 
v_toFunctor_683_ = lean_ctor_get(v_toApplicative_679_, 0);
v_toSeq_684_ = lean_ctor_get(v_toApplicative_679_, 2);
v_toSeqLeft_685_ = lean_ctor_get(v_toApplicative_679_, 3);
v_toSeqRight_686_ = lean_ctor_get(v_toApplicative_679_, 4);
v_isSharedCheck_720_ = !lean_is_exclusive(v_toApplicative_679_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_toApplicative_679_, 1);
lean_dec(v_unused_721_);
v___x_688_ = v_toApplicative_679_;
v_isShared_689_ = v_isSharedCheck_720_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_toSeqRight_686_);
lean_inc(v_toSeqLeft_685_);
lean_inc(v_toSeq_684_);
lean_inc(v_toFunctor_683_);
lean_dec(v_toApplicative_679_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_720_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___x_697_; 
lean_inc_ref(v_toFunctor_683_);
v___f_690_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_690_, 0, v_toFunctor_683_);
v___f_691_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_691_, 0, v_toFunctor_683_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___f_690_);
lean_ctor_set(v___x_692_, 1, v___f_691_);
v___f_693_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_693_, 0, v_toSeqRight_686_);
v___f_694_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_694_, 0, v_toSeqLeft_685_);
v___f_695_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_695_, 0, v_toSeq_684_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 4, v___f_693_);
lean_ctor_set(v___x_688_, 3, v___f_694_);
lean_ctor_set(v___x_688_, 2, v___f_695_);
lean_ctor_set(v___x_688_, 1, v___f_644_);
lean_ctor_set(v___x_688_, 0, v___x_692_);
v___x_697_ = v___x_688_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___f_644_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v___f_695_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v___f_694_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v___f_693_);
v___x_697_ = v_reuseFailAlloc_719_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___f_645_);
lean_ctor_set(v___x_681_, 0, v___x_697_);
v___x_699_ = v___x_681_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___f_645_);
v___x_699_ = v_reuseFailAlloc_718_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_toMonadRef_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_toApplicative_709_; lean_object* v_toBind_710_; lean_object* v_toPure_711_; lean_object* v_liftWith_712_; lean_object* v_restoreM_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_700_ = l_StateRefT_x27_instMonad___redArg(v___x_699_);
v___x_701_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_701_, 0, lean_box(0));
lean_closure_set(v___x_701_, 1, lean_box(0));
lean_closure_set(v___x_701_, 2, v___x_700_);
v___x_702_ = l_instMonadControlTOfPure___redArg(v___x_701_);
v___x_703_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_704_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19);
v_toMonadRef_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_toMonadRef_705_);
v___x_706_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_678_);
v___x_707_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_706_, v___x_678_);
v___x_708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_708_, 0, v___x_703_);
lean_ctor_set(v___x_708_, 1, v_toMonadRef_705_);
lean_ctor_set(v___x_708_, 2, v___x_707_);
v_toApplicative_709_ = lean_ctor_get(v_inst_629_, 0);
lean_inc_ref(v_toApplicative_709_);
v_toBind_710_ = lean_ctor_get(v_inst_629_, 1);
lean_inc(v_toBind_710_);
lean_dec_ref(v_inst_629_);
v_toPure_711_ = lean_ctor_get(v_toApplicative_709_, 1);
lean_inc(v_toPure_711_);
lean_dec_ref(v_toApplicative_709_);
v_liftWith_712_ = lean_ctor_get(v_inst_630_, 0);
lean_inc(v_liftWith_712_);
v_restoreM_713_ = lean_ctor_get(v_inst_630_, 1);
lean_inc(v_restoreM_713_);
lean_dec_ref(v_inst_630_);
lean_inc(v_toBind_710_);
v___f_714_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed), 15, 9);
lean_closure_set(v___f_714_, 0, v_goal_632_);
lean_closure_set(v___f_714_, 1, v___x_678_);
lean_closure_set(v___f_714_, 2, v___x_708_);
lean_closure_set(v___f_714_, 3, v_toPure_711_);
lean_closure_set(v___f_714_, 4, v_ident_633_);
lean_closure_set(v___f_714_, 5, v_inst_631_);
lean_closure_set(v___f_714_, 6, v_toBind_710_);
lean_closure_set(v___f_714_, 7, v_k_634_);
lean_closure_set(v___f_714_, 8, v___x_702_);
v___x_715_ = lean_apply_2(v_liftWith_712_, lean_box(0), v___f_714_);
v___x_716_ = lean_apply_1(v_restoreM_713_, lean_box(0));
v___x_717_ = lean_apply_4(v_toBind_710_, lean_box(0), lean_box(0), v___x_715_, v___x_716_);
return v___x_717_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall(lean_object* v_m_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_goal_737_, lean_object* v_ident_738_, lean_object* v_k_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_734_, v_inst_735_, v_inst_736_, v_goal_737_, v_ident_738_, v_k_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(uint8_t v_isZero_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_ref_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_ref_756_ = lean_ctor_get(v___y_753_, 5);
v___x_757_ = l_Lean_SourceInfo_fromRef(v_ref_756_, v_isZero_750_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3));
v___x_760_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4));
lean_inc(v___x_757_);
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_757_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
lean_inc(v___x_757_);
v___x_762_ = l_Lean_Syntax_node1(v___x_757_, v___x_759_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___x_757_, v___x_758_, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed(lean_object* v_isZero_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_isZero_boxed_771_; lean_object* v_res_772_; 
v_isZero_boxed_771_ = lean_unbox(v_isZero_765_);
v_res_772_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(v_isZero_boxed_771_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2(lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_goal_776_, lean_object* v___f_777_, lean_object* v_____do__lift_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_773_, v_inst_774_, v_inst_775_, v_goal_776_, v_____do__lift_778_, v___f_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed(lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_n_783_, lean_object* v_k_784_, lean_object* v_g_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(v_inst_780_, v_inst_781_, v_inst_782_, v_n_783_, v_k_784_, v_g_785_);
lean_dec(v_n_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_goal_790_, lean_object* v_n_791_, lean_object* v_k_792_){
_start:
{
lean_object* v_toBind_793_; lean_object* v_zero_794_; uint8_t v_isZero_795_; 
v_toBind_793_ = lean_ctor_get(v_inst_787_, 1);
lean_inc(v_toBind_793_);
v_zero_794_ = lean_unsigned_to_nat(0u);
v_isZero_795_ = lean_nat_dec_eq(v_n_791_, v_zero_794_);
if (v_isZero_795_ == 1)
{
lean_object* v___x_796_; 
lean_dec(v_toBind_793_);
lean_dec(v_inst_789_);
lean_dec_ref(v_inst_788_);
lean_dec_ref(v_inst_787_);
v___x_796_ = lean_apply_1(v_k_792_, v_goal_790_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___f_798_; lean_object* v_one_799_; lean_object* v_n_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_797_ = lean_box(v_isZero_795_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_798_, 0, v___x_797_);
v_one_799_ = lean_unsigned_to_nat(1u);
v_n_800_ = lean_nat_sub(v_n_791_, v_one_799_);
lean_inc(v_inst_789_);
lean_inc_ref(v_inst_788_);
lean_inc_ref(v_inst_787_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_801_, 0, v_inst_787_);
lean_closure_set(v___f_801_, 1, v_inst_788_);
lean_closure_set(v___f_801_, 2, v_inst_789_);
lean_closure_set(v___f_801_, 3, v_n_800_);
lean_closure_set(v___f_801_, 4, v_k_792_);
lean_inc(v_inst_789_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2), 6, 5);
lean_closure_set(v___f_802_, 0, v_inst_787_);
lean_closure_set(v___f_802_, 1, v_inst_788_);
lean_closure_set(v___f_802_, 2, v_inst_789_);
lean_closure_set(v___f_802_, 3, v_goal_790_);
lean_closure_set(v___f_802_, 4, v___f_801_);
v___x_803_ = lean_apply_2(v_inst_789_, lean_box(0), v___f_798_);
v___x_804_ = lean_apply_4(v_toBind_793_, lean_box(0), lean_box(0), v___x_803_, v___f_802_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_n_808_, lean_object* v_k_809_, lean_object* v_g_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_805_, v_inst_806_, v_inst_807_, v_g_810_, v_n_808_, v_k_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___boxed(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_goal_815_, lean_object* v_n_816_, lean_object* v_k_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_812_, v_inst_813_, v_inst_814_, v_goal_815_, v_n_816_, v_k_817_);
lean_dec(v_n_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(lean_object* v_m_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_goal_823_, lean_object* v_n_824_, lean_object* v_k_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_820_, v_inst_821_, v_inst_822_, v_goal_823_, v_n_824_, v_k_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___boxed(lean_object* v_m_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_goal_831_, lean_object* v_n_832_, lean_object* v_k_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(v_m_827_, v_inst_828_, v_inst_829_, v_inst_830_, v_goal_831_, v_n_832_, v_k_833_);
lean_dec(v_n_832_);
return v_res_834_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10));
v___x_864_ = l_String_toRawSubstring_x27(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0));
v___x_879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_875_);
v___x_880_ = l_Lean_Syntax_isOfKind(v_x_875_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_a_876_);
lean_dec(v_x_875_);
v___x_881_ = lean_box(1);
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_877_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = l_Lean_Syntax_getArg(v_x_875_, v___x_884_);
lean_dec(v_x_875_);
v___x_886_ = lean_unsigned_to_nat(2u);
v___x_887_ = l_Lean_Syntax_getNumArgs(v___x_885_);
v___x_888_ = lean_nat_dec_le(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
uint8_t v___x_889_; 
lean_dec(v___x_887_);
lean_inc(v___x_885_);
v___x_889_ = l_Lean_Syntax_matchesNull(v___x_885_, v___x_884_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v___x_885_);
lean_dec_ref(v_a_876_);
v___x_890_ = lean_box(1);
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_a_877_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_892_ = l_Lean_Syntax_getArg(v___x_885_, v___x_883_);
lean_dec(v___x_885_);
v___x_893_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_892_);
v___x_894_ = l_Lean_Syntax_isOfKind(v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v___x_892_);
lean_dec_ref(v_a_876_);
v___x_895_ = l_Lean_Macro_throwUnsupported___redArg(v_a_877_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = l_Lean_Syntax_getArg(v___x_892_, v___x_883_);
lean_dec(v___x_892_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_896_);
v___x_898_ = l_Lean_Syntax_isOfKind(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v_quotContext_899_; lean_object* v_currMacroScope_900_; lean_object* v_ref_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_quotContext_899_ = lean_ctor_get(v_a_876_, 1);
lean_inc(v_quotContext_899_);
v_currMacroScope_900_ = lean_ctor_get(v_a_876_, 2);
lean_inc(v_currMacroScope_900_);
v_ref_901_ = lean_ctor_get(v_a_876_, 5);
lean_inc(v_ref_901_);
lean_dec_ref(v_a_876_);
v___x_902_ = l_Lean_SourceInfo_fromRef(v_ref_901_, v___x_898_);
lean_dec(v_ref_901_);
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc(v___x_902_);
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_902_);
lean_ctor_set(v___x_905_, 1, v___x_878_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_907_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
v___x_909_ = l_Lean_addMacroScope(v_quotContext_899_, v___x_908_, v_currMacroScope_900_);
v___x_910_ = lean_box(0);
lean_inc(v___x_902_);
v___x_911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_911_, 0, v___x_902_);
lean_ctor_set(v___x_911_, 1, v___x_907_);
lean_ctor_set(v___x_911_, 2, v___x_909_);
lean_ctor_set(v___x_911_, 3, v___x_910_);
lean_inc_ref(v___x_911_);
lean_inc(v___x_902_);
v___x_912_ = l_Lean_Syntax_node1(v___x_902_, v___x_906_, v___x_911_);
lean_inc(v___x_902_);
v___x_913_ = l_Lean_Syntax_node1(v___x_902_, v___x_897_, v___x_912_);
lean_inc(v___x_902_);
v___x_914_ = l_Lean_Syntax_node1(v___x_902_, v___x_893_, v___x_913_);
lean_inc(v___x_902_);
v___x_915_ = l_Lean_Syntax_node1(v___x_902_, v___x_904_, v___x_914_);
lean_inc(v___x_902_);
v___x_916_ = l_Lean_Syntax_node2(v___x_902_, v___x_879_, v___x_905_, v___x_915_);
v___x_917_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
lean_inc(v___x_902_);
v___x_918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_902_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_920_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
lean_inc(v___x_902_);
v___x_921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_902_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
v___x_922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
lean_inc(v___x_902_);
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_902_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
lean_inc(v___x_902_);
v___x_924_ = l_Lean_Syntax_node4(v___x_902_, v___x_920_, v___x_921_, v___x_911_, v___x_923_, v___x_896_);
lean_inc(v___x_902_);
v___x_925_ = l_Lean_Syntax_node3(v___x_902_, v___x_904_, v___x_916_, v___x_918_, v___x_924_);
v___x_926_ = l_Lean_Syntax_node1(v___x_902_, v___x_903_, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_877_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = l_Lean_Syntax_getArg(v___x_896_, v___x_883_);
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_930_ = l_Lean_Syntax_isOfKind(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v_quotContext_931_; lean_object* v_currMacroScope_932_; lean_object* v_ref_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_quotContext_931_ = lean_ctor_get(v_a_876_, 1);
lean_inc(v_quotContext_931_);
v_currMacroScope_932_ = lean_ctor_get(v_a_876_, 2);
lean_inc(v_currMacroScope_932_);
v_ref_933_ = lean_ctor_get(v_a_876_, 5);
lean_inc(v_ref_933_);
lean_dec_ref(v_a_876_);
v___x_934_ = l_Lean_SourceInfo_fromRef(v_ref_933_, v___x_930_);
lean_dec(v_ref_933_);
v___x_935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc(v___x_934_);
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_934_);
lean_ctor_set(v___x_937_, 1, v___x_878_);
v___x_938_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
v___x_940_ = l_Lean_addMacroScope(v_quotContext_931_, v___x_939_, v_currMacroScope_932_);
v___x_941_ = lean_box(0);
lean_inc(v___x_934_);
v___x_942_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_942_, 0, v___x_934_);
lean_ctor_set(v___x_942_, 1, v___x_938_);
lean_ctor_set(v___x_942_, 2, v___x_940_);
lean_ctor_set(v___x_942_, 3, v___x_941_);
lean_inc_ref(v___x_942_);
lean_inc(v___x_934_);
v___x_943_ = l_Lean_Syntax_node1(v___x_934_, v___x_929_, v___x_942_);
lean_inc(v___x_934_);
v___x_944_ = l_Lean_Syntax_node1(v___x_934_, v___x_897_, v___x_943_);
lean_inc(v___x_934_);
v___x_945_ = l_Lean_Syntax_node1(v___x_934_, v___x_893_, v___x_944_);
lean_inc(v___x_934_);
v___x_946_ = l_Lean_Syntax_node1(v___x_934_, v___x_936_, v___x_945_);
lean_inc(v___x_934_);
v___x_947_ = l_Lean_Syntax_node2(v___x_934_, v___x_879_, v___x_937_, v___x_946_);
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
lean_inc(v___x_934_);
v___x_949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_934_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_951_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
lean_inc(v___x_934_);
v___x_952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_934_);
lean_ctor_set(v___x_952_, 1, v___x_950_);
v___x_953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
lean_inc(v___x_934_);
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_934_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
lean_inc(v___x_934_);
v___x_955_ = l_Lean_Syntax_node4(v___x_934_, v___x_951_, v___x_952_, v___x_942_, v___x_954_, v___x_896_);
lean_inc(v___x_934_);
v___x_956_ = l_Lean_Syntax_node3(v___x_934_, v___x_936_, v___x_947_, v___x_949_, v___x_955_);
v___x_957_ = l_Lean_Syntax_node1(v___x_934_, v___x_935_, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_a_877_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v___x_896_);
lean_dec_ref(v_a_876_);
v___x_959_ = l_Lean_Macro_throwUnsupported___redArg(v_a_877_);
return v___x_959_;
}
}
}
}
}
else
{
lean_object* v_ref_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_pats_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_ref_960_ = lean_ctor_get(v_a_876_, 5);
lean_inc(v_ref_960_);
lean_dec_ref(v_a_876_);
v___x_961_ = l_Lean_Syntax_getArg(v___x_885_, v___x_883_);
v___x_962_ = l_Lean_Syntax_getArg(v___x_885_, v___x_884_);
v___x_963_ = l_Lean_Syntax_getArgs(v___x_885_);
lean_dec(v___x_885_);
v___x_964_ = l_Array_extract___redArg(v___x_963_, v___x_886_, v___x_887_);
lean_dec_ref(v___x_963_);
v___x_965_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
v___x_966_ = lean_box(2);
v___x_967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_965_);
lean_ctor_set(v___x_967_, 2, v___x_964_);
v_pats_968_ = l_Lean_Syntax_getArgs(v___x_967_);
lean_dec_ref(v___x_967_);
v___x_969_ = 0;
v___x_970_ = l_Lean_SourceInfo_fromRef(v_ref_960_, v___x_969_);
lean_dec(v_ref_960_);
v___x_971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
lean_inc(v___x_970_);
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_878_);
lean_inc(v___x_970_);
v___x_973_ = l_Lean_Syntax_node1(v___x_970_, v___x_965_, v___x_961_);
lean_inc_ref(v___x_972_);
lean_inc(v___x_970_);
v___x_974_ = l_Lean_Syntax_node2(v___x_970_, v___x_879_, v___x_972_, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
lean_inc(v___x_970_);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_970_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Array_mkArray1___redArg(v___x_962_);
v___x_978_ = l_Array_append___redArg(v___x_977_, v_pats_968_);
lean_dec_ref(v_pats_968_);
lean_inc(v___x_970_);
v___x_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_979_, 0, v___x_970_);
lean_ctor_set(v___x_979_, 1, v___x_965_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
lean_inc(v___x_970_);
v___x_980_ = l_Lean_Syntax_node2(v___x_970_, v___x_879_, v___x_972_, v___x_979_);
lean_inc(v___x_970_);
v___x_981_ = l_Lean_Syntax_node3(v___x_970_, v___x_965_, v___x_974_, v___x_976_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___x_970_, v___x_971_, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_a_877_);
return v___x_983_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_box(0);
v___x_985_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0);
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___boxed(lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(lean_object* v_00_u03b1_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___boxed(lean_object* v_00_u03b1_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(v_00_u03b1_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
v___x_1024_ = lean_apply_9(v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed(lean_object* v_x_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(v_x_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(lean_object* v_mvarId_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___f_1047_; lean_object* v___x_1048_; 
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1047_, 0, v_x_1037_);
lean_closure_set(v___f_1047_, 1, v___y_1038_);
lean_closure_set(v___f_1047_, 2, v___y_1039_);
lean_closure_set(v___f_1047_, 3, v___y_1040_);
lean_closure_set(v___f_1047_, 4, v___y_1041_);
v___x_1048_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1036_, v___f_1047_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1048_) == 0)
{
return v___x_1048_;
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___boxed(lean_object* v_mvarId_1057_, lean_object* v_x_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1057_, v_x_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(lean_object* v_00_u03b1_1069_, lean_object* v_mvarId_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1070_, v_x_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___boxed(lean_object* v_00_u03b1_1082_, lean_object* v_mvarId_1083_, lean_object* v_x_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(v_00_u03b1_1082_, v_mvarId_1083_, v_x_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(lean_object* v_val_1095_, lean_object* v_newGoal_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1096_);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1106_, v___x_1107_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1120_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1113_ = lean_st_ref_take(v_val_1095_);
v___x_1114_ = l_Lean_Expr_mvarId_x21(v_a_1109_);
v___x_1115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1113_);
v___x_1116_ = lean_st_ref_set(v_val_1095_, v___x_1115_);
if (v_isShared_1112_ == 0)
{
v___x_1118_ = v___x_1111_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1109_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed(lean_object* v_val_1121_, lean_object* v_newGoal_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(v_val_1121_, v_newGoal_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v_val_1121_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
lean_object* v_ks_1137_; lean_object* v_vs_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1162_; 
v_ks_1137_ = lean_ctor_get(v_x_1133_, 0);
v_vs_1138_ = lean_ctor_get(v_x_1133_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1140_ = v_x_1133_;
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_vs_1138_);
lean_inc(v_ks_1137_);
lean_dec(v_x_1133_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_array_get_size(v_ks_1137_);
v___x_1143_ = lean_nat_dec_lt(v_x_1134_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_x_1134_);
v___x_1144_ = lean_array_push(v_ks_1137_, v_x_1135_);
v___x_1145_ = lean_array_push(v_vs_1138_, v_x_1136_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1145_);
lean_ctor_set(v___x_1140_, 0, v___x_1144_);
v___x_1147_ = v___x_1140_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v_k_x27_1149_; uint8_t v___x_1150_; 
v_k_x27_1149_ = lean_array_fget_borrowed(v_ks_1137_, v_x_1134_);
v___x_1150_ = l_Lean_instBEqMVarId_beq(v_x_1135_, v_k_x27_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; 
if (v_isShared_1141_ == 0)
{
v___x_1152_ = v___x_1140_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_ks_1137_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_vs_1138_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_x_1134_, v___x_1153_);
lean_dec(v_x_1134_);
v_x_1133_ = v___x_1152_;
v_x_1134_ = v___x_1154_;
goto _start;
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1157_ = lean_array_fset(v_ks_1137_, v_x_1134_, v_x_1135_);
v___x_1158_ = lean_array_fset(v_vs_1138_, v_x_1134_, v_x_1136_);
lean_dec(v_x_1134_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1158_);
lean_ctor_set(v___x_1140_, 0, v___x_1157_);
v___x_1160_ = v___x_1140_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_n_1163_, lean_object* v_k_1164_, lean_object* v_v_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_n_1163_, v___x_1166_, v_k_1164_, v_v_1165_);
return v___x_1167_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; 
v___x_1168_ = ((size_t)5ULL);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_shift_left(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; 
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0);
v___x_1173_ = lean_usize_sub(v___x_1172_, v___x_1171_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(lean_object* v_x_1175_, size_t v_x_1176_, size_t v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_object* v_es_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v_j_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_es_1180_ = lean_ctor_get(v_x_1175_, 0);
v___x_1181_ = ((size_t)5ULL);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1);
v___x_1184_ = lean_usize_land(v_x_1176_, v___x_1183_);
v_j_1185_ = lean_usize_to_nat(v___x_1184_);
v___x_1186_ = lean_array_get_size(v_es_1180_);
v___x_1187_ = lean_nat_dec_lt(v_j_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_dec(v_j_1185_);
lean_dec(v_x_1179_);
lean_dec(v_x_1178_);
return v_x_1175_;
}
else
{
lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1224_; 
lean_inc_ref(v_es_1180_);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_x_1175_, 0);
lean_dec(v_unused_1225_);
v___x_1189_ = v_x_1175_;
v_isShared_1190_ = v_isSharedCheck_1224_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v_x_1175_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1224_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_v_1191_; lean_object* v___x_1192_; lean_object* v_xs_x27_1193_; lean_object* v___y_1195_; 
v_v_1191_ = lean_array_fget(v_es_1180_, v_j_1185_);
v___x_1192_ = lean_box(0);
v_xs_x27_1193_ = lean_array_fset(v_es_1180_, v_j_1185_, v___x_1192_);
switch(lean_obj_tag(v_v_1191_))
{
case 0:
{
lean_object* v_key_1200_; lean_object* v_val_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1211_; 
v_key_1200_ = lean_ctor_get(v_v_1191_, 0);
v_val_1201_ = lean_ctor_get(v_v_1191_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_v_1191_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1203_ = v_v_1191_;
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_val_1201_);
lean_inc(v_key_1200_);
lean_dec(v_v_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_instBEqMVarId_beq(v_x_1178_, v_key_1200_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_del_object(v___x_1203_);
v___x_1206_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1200_, v_val_1201_, v_x_1178_, v_x_1179_);
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
v___y_1195_ = v___x_1207_;
goto v___jp_1194_;
}
else
{
lean_object* v___x_1209_; 
lean_dec(v_val_1201_);
lean_dec(v_key_1200_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_x_1179_);
lean_ctor_set(v___x_1203_, 0, v_x_1178_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_x_1178_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_x_1179_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
v___y_1195_ = v___x_1209_;
goto v___jp_1194_;
}
}
}
}
case 1:
{
lean_object* v_node_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v_node_1212_ = lean_ctor_get(v_v_1191_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_v_1191_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1214_ = v_v_1191_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_node_1212_);
lean_dec(v_v_1191_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1216_ = lean_usize_shift_right(v_x_1176_, v___x_1181_);
v___x_1217_ = lean_usize_add(v_x_1177_, v___x_1182_);
v___x_1218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_node_1212_, v___x_1216_, v___x_1217_, v_x_1178_, v_x_1179_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1218_);
v___x_1220_ = v___x_1214_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v___y_1195_ = v___x_1220_;
goto v___jp_1194_;
}
}
}
default: 
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_x_1178_);
lean_ctor_set(v___x_1223_, 1, v_x_1179_);
v___y_1195_ = v___x_1223_;
goto v___jp_1194_;
}
}
v___jp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_array_fset(v_xs_x27_1193_, v_j_1185_, v___y_1195_);
lean_dec(v_j_1185_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1196_);
v___x_1198_ = v___x_1189_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
else
{
lean_object* v_ks_1226_; lean_object* v_vs_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1247_; 
v_ks_1226_ = lean_ctor_get(v_x_1175_, 0);
v_vs_1227_ = lean_ctor_get(v_x_1175_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1229_ = v_x_1175_;
v_isShared_1230_ = v_isSharedCheck_1247_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_vs_1227_);
lean_inc(v_ks_1226_);
lean_dec(v_x_1175_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1247_;
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
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_ks_1226_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_vs_1227_);
v___x_1232_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v_newNode_1233_; uint8_t v___y_1235_; size_t v___x_1241_; uint8_t v___x_1242_; 
v_newNode_1233_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v___x_1232_, v_x_1178_, v_x_1179_);
v___x_1241_ = ((size_t)7ULL);
v___x_1242_ = lean_usize_dec_le(v___x_1241_, v_x_1177_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1233_);
v___x_1244_ = lean_unsigned_to_nat(4u);
v___x_1245_ = lean_nat_dec_lt(v___x_1243_, v___x_1244_);
lean_dec(v___x_1243_);
v___y_1235_ = v___x_1245_;
goto v___jp_1234_;
}
else
{
v___y_1235_ = v___x_1242_;
goto v___jp_1234_;
}
v___jp_1234_:
{
if (v___y_1235_ == 0)
{
lean_object* v_ks_1236_; lean_object* v_vs_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_ks_1236_ = lean_ctor_get(v_newNode_1233_, 0);
lean_inc_ref(v_ks_1236_);
v_vs_1237_ = lean_ctor_get(v_newNode_1233_, 1);
lean_inc_ref(v_vs_1237_);
lean_dec_ref(v_newNode_1233_);
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2);
v___x_1240_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_x_1177_, v_ks_1236_, v_vs_1237_, v___x_1238_, v___x_1239_);
lean_dec_ref(v_vs_1237_);
lean_dec_ref(v_ks_1236_);
return v___x_1240_;
}
else
{
return v_newNode_1233_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(size_t v_depth_1248_, lean_object* v_keys_1249_, lean_object* v_vals_1250_, lean_object* v_i_1251_, lean_object* v_entries_1252_){
_start:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_array_get_size(v_keys_1249_);
v___x_1254_ = lean_nat_dec_lt(v_i_1251_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec(v_i_1251_);
return v_entries_1252_;
}
else
{
lean_object* v_k_1255_; lean_object* v_v_1256_; uint64_t v___x_1257_; size_t v_h_1258_; size_t v___x_1259_; lean_object* v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v_h_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_k_1255_ = lean_array_fget_borrowed(v_keys_1249_, v_i_1251_);
v_v_1256_ = lean_array_fget_borrowed(v_vals_1250_, v_i_1251_);
v___x_1257_ = l_Lean_instHashableMVarId_hash(v_k_1255_);
v_h_1258_ = lean_uint64_to_usize(v___x_1257_);
v___x_1259_ = ((size_t)5ULL);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_sub(v_depth_1248_, v___x_1261_);
v___x_1263_ = lean_usize_mul(v___x_1259_, v___x_1262_);
v_h_1264_ = lean_usize_shift_right(v_h_1258_, v___x_1263_);
v___x_1265_ = lean_nat_add(v_i_1251_, v___x_1260_);
lean_dec(v_i_1251_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
v___x_1266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_entries_1252_, v_h_1264_, v_depth_1248_, v_k_1255_, v_v_1256_);
v_i_1251_ = v___x_1265_;
v_entries_1252_ = v___x_1266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_depth_1268_, lean_object* v_keys_1269_, lean_object* v_vals_1270_, lean_object* v_i_1271_, lean_object* v_entries_1272_){
_start:
{
size_t v_depth_boxed_1273_; lean_object* v_res_1274_; 
v_depth_boxed_1273_ = lean_unbox_usize(v_depth_1268_);
lean_dec(v_depth_1268_);
v_res_1274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_boxed_1273_, v_keys_1269_, v_vals_1270_, v_i_1271_, v_entries_1272_);
lean_dec_ref(v_vals_1270_);
lean_dec_ref(v_keys_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
size_t v_x_20306__boxed_1280_; size_t v_x_20307__boxed_1281_; lean_object* v_res_1282_; 
v_x_20306__boxed_1280_ = lean_unbox_usize(v_x_1276_);
lean_dec(v_x_1276_);
v_x_20307__boxed_1281_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_res_1282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1275_, v_x_20306__boxed_1280_, v_x_20307__boxed_1281_, v_x_1278_, v_x_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
uint64_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = l_Lean_instHashableMVarId_hash(v_x_1284_);
v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1283_, v___x_1287_, v___x_1288_, v_x_1284_, v_x_1285_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(lean_object* v_mvarId_1290_, lean_object* v_val_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v_mctx_1295_; lean_object* v_cache_1296_; lean_object* v_zetaDeltaFVarIds_1297_; lean_object* v_postponed_1298_; lean_object* v_diag_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1326_; 
v___x_1294_ = lean_st_ref_take(v___y_1292_);
v_mctx_1295_ = lean_ctor_get(v___x_1294_, 0);
v_cache_1296_ = lean_ctor_get(v___x_1294_, 1);
v_zetaDeltaFVarIds_1297_ = lean_ctor_get(v___x_1294_, 2);
v_postponed_1298_ = lean_ctor_get(v___x_1294_, 3);
v_diag_1299_ = lean_ctor_get(v___x_1294_, 4);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1301_ = v___x_1294_;
v_isShared_1302_ = v_isSharedCheck_1326_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_diag_1299_);
lean_inc(v_postponed_1298_);
lean_inc(v_zetaDeltaFVarIds_1297_);
lean_inc(v_cache_1296_);
lean_inc(v_mctx_1295_);
lean_dec(v___x_1294_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1326_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v_depth_1303_; lean_object* v_levelAssignDepth_1304_; lean_object* v_mvarCounter_1305_; lean_object* v_lDepth_1306_; lean_object* v_decls_1307_; lean_object* v_userNames_1308_; lean_object* v_lAssignment_1309_; lean_object* v_eAssignment_1310_; lean_object* v_dAssignment_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1325_; 
v_depth_1303_ = lean_ctor_get(v_mctx_1295_, 0);
v_levelAssignDepth_1304_ = lean_ctor_get(v_mctx_1295_, 1);
v_mvarCounter_1305_ = lean_ctor_get(v_mctx_1295_, 2);
v_lDepth_1306_ = lean_ctor_get(v_mctx_1295_, 3);
v_decls_1307_ = lean_ctor_get(v_mctx_1295_, 4);
v_userNames_1308_ = lean_ctor_get(v_mctx_1295_, 5);
v_lAssignment_1309_ = lean_ctor_get(v_mctx_1295_, 6);
v_eAssignment_1310_ = lean_ctor_get(v_mctx_1295_, 7);
v_dAssignment_1311_ = lean_ctor_get(v_mctx_1295_, 8);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_mctx_1295_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1313_ = v_mctx_1295_;
v_isShared_1314_ = v_isSharedCheck_1325_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_dAssignment_1311_);
lean_inc(v_eAssignment_1310_);
lean_inc(v_lAssignment_1309_);
lean_inc(v_userNames_1308_);
lean_inc(v_decls_1307_);
lean_inc(v_lDepth_1306_);
lean_inc(v_mvarCounter_1305_);
lean_inc(v_levelAssignDepth_1304_);
lean_inc(v_depth_1303_);
lean_dec(v_mctx_1295_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1325_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_eAssignment_1310_, v_mvarId_1290_, v_val_1291_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 7, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_depth_1303_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_levelAssignDepth_1304_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_mvarCounter_1305_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_lDepth_1306_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v_decls_1307_);
lean_ctor_set(v_reuseFailAlloc_1324_, 5, v_userNames_1308_);
lean_ctor_set(v_reuseFailAlloc_1324_, 6, v_lAssignment_1309_);
lean_ctor_set(v_reuseFailAlloc_1324_, 7, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1324_, 8, v_dAssignment_1311_);
v___x_1317_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1317_);
v___x_1319_ = v___x_1301_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_cache_1296_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_zetaDeltaFVarIds_1297_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_postponed_1298_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_diag_1299_);
v___x_1319_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_st_ref_set(v___y_1292_, v___x_1319_);
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(lean_object* v_mvarId_1327_, lean_object* v_val_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_1327_, v_val_1328_, v___y_1329_);
lean_dec(v___y_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_k_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1339_ = lean_apply_6(v_k_1332_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, lean_box(0));
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_k_1340_, lean_object* v_b_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_1340_, v_b_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(lean_object* v_name_1348_, uint8_t v_bi_1349_, lean_object* v_type_1350_, lean_object* v_k_1351_, uint8_t v_kind_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___f_1358_; lean_object* v___x_1359_; 
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1358_, 0, v_k_1351_);
v___x_1359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1348_, v_bi_1349_, v_type_1350_, v___f_1358_, v_kind_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_name_1376_, lean_object* v_bi_1377_, lean_object* v_type_1378_, lean_object* v_k_1379_, lean_object* v_kind_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_bi_boxed_1386_; uint8_t v_kind_boxed_1387_; lean_object* v_res_1388_; 
v_bi_boxed_1386_ = lean_unbox(v_bi_1377_);
v_kind_boxed_1387_ = lean_unbox(v_kind_1380_);
v_res_1388_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1376_, v_bi_boxed_1386_, v_type_1378_, v_k_1379_, v_kind_boxed_1387_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(lean_object* v_name_1389_, lean_object* v_type_1390_, lean_object* v_k_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = 0;
v___x_1398_ = 0;
v___x_1399_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1389_, v___x_1397_, v_type_1390_, v_k_1391_, v___x_1398_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(lean_object* v_name_1400_, lean_object* v_type_1401_, lean_object* v_k_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_1400_, v_type_1401_, v_k_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(lean_object* v_msgData_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v_env_1416_; lean_object* v___x_1417_; lean_object* v_mctx_1418_; lean_object* v_lctx_1419_; lean_object* v_options_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1415_ = lean_st_ref_get(v___y_1413_);
v_env_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc_ref(v_env_1416_);
lean_dec(v___x_1415_);
v___x_1417_ = lean_st_ref_get(v___y_1411_);
v_mctx_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_mctx_1418_);
lean_dec(v___x_1417_);
v_lctx_1419_ = lean_ctor_get(v___y_1410_, 2);
v_options_1420_ = lean_ctor_get(v___y_1412_, 2);
lean_inc_ref(v_options_1420_);
lean_inc_ref(v_lctx_1419_);
v___x_1421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1421_, 0, v_env_1416_);
lean_ctor_set(v___x_1421_, 1, v_mctx_1418_);
lean_ctor_set(v___x_1421_, 2, v_lctx_1419_);
lean_ctor_set(v___x_1421_, 3, v_options_1420_);
v___x_1422_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v_msgData_1409_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(lean_object* v_msg_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_ref_1437_; lean_object* v___x_1438_; lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
v_ref_1437_ = lean_ctor_get(v___y_1434_, 5);
v___x_1438_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msg_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_inc(v_ref_1437_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_ref_1437_);
lean_ctor_set(v___x_1443_, 1, v_a_1439_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 1);
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(lean_object* v___x_1455_, lean_object* v_ident_1456_, uint8_t v___x_1457_, lean_object* v_hyps_1458_, lean_object* v___x_1459_, lean_object* v_target_1460_, lean_object* v_u_1461_, lean_object* v_k_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v_s_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_lctx_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_lctx_1473_ = lean_ctor_get(v___y_1468_, 2);
lean_inc_ref(v___x_1455_);
v___x_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1455_);
lean_inc_ref(v_s_1467_);
lean_inc_ref(v_lctx_1473_);
v___x_1475_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_1456_, v_lctx_1473_, v_s_1467_, v___x_1474_, v___x_1457_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v___x_1475_);
lean_inc_ref(v_s_1467_);
lean_inc_ref(v_hyps_1458_);
v___x_1476_ = l_Lean_Expr_app___override(v_hyps_1458_, v_s_1467_);
lean_inc_ref(v___x_1459_);
v___x_1477_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_1459_, v___x_1476_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1478_);
v___x_1480_ = lean_array_push(v___x_1479_, v_s_1467_);
v___x_1481_ = 0;
lean_inc_ref(v_target_1460_);
v___x_1482_ = l_Lean_Expr_betaRev(v_target_1460_, v___x_1480_, v___x_1481_, v___x_1481_);
lean_inc_ref(v___x_1459_);
lean_inc(v_u_1461_);
v___x_1483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1483_, 0, v_u_1461_);
lean_ctor_set(v___x_1483_, 1, v___x_1459_);
lean_ctor_set(v___x_1483_, 2, v___x_1477_);
lean_ctor_set(v___x_1483_, 3, v___x_1482_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
v___x_1484_ = lean_apply_10(v_k_1462_, v___x_1483_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = 1;
v___x_1487_ = l_Lean_Meta_mkLambdaFVars(v___x_1480_, v_a_1485_, v___x_1481_, v___x_1457_, v___x_1481_, v___x_1457_, v___x_1486_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___x_1480_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1500_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_u_1461_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_mkConst(v___x_1492_, v___x_1494_);
v___x_1496_ = l_Lean_mkApp5(v___x_1495_, v___x_1459_, v___x_1455_, v_hyps_1458_, v_target_1460_, v_a_1488_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1496_);
v___x_1498_ = v___x_1490_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
else
{
lean_dec(v_u_1461_);
lean_dec_ref(v_target_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_hyps_1458_);
lean_dec_ref(v___x_1455_);
return v___x_1487_;
}
}
else
{
lean_dec_ref(v___x_1480_);
lean_dec_ref(v___y_1468_);
lean_dec(v_u_1461_);
lean_dec_ref(v_target_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_hyps_1458_);
lean_dec_ref(v___x_1455_);
return v___x_1484_;
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_s_1467_);
lean_dec_ref(v_k_1462_);
lean_dec(v_u_1461_);
lean_dec_ref(v_target_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_hyps_1458_);
lean_dec_ref(v___x_1455_);
v_a_1501_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1475_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1475_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_1509_ = _args[0];
lean_object* v_ident_1510_ = _args[1];
lean_object* v___x_1511_ = _args[2];
lean_object* v_hyps_1512_ = _args[3];
lean_object* v___x_1513_ = _args[4];
lean_object* v_target_1514_ = _args[5];
lean_object* v_u_1515_ = _args[6];
lean_object* v_k_1516_ = _args[7];
lean_object* v___y_1517_ = _args[8];
lean_object* v___y_1518_ = _args[9];
lean_object* v___y_1519_ = _args[10];
lean_object* v___y_1520_ = _args[11];
lean_object* v_s_1521_ = _args[12];
lean_object* v___y_1522_ = _args[13];
lean_object* v___y_1523_ = _args[14];
lean_object* v___y_1524_ = _args[15];
lean_object* v___y_1525_ = _args[16];
lean_object* v___y_1526_ = _args[17];
_start:
{
uint8_t v___x_20685__boxed_1527_; lean_object* v_res_1528_; 
v___x_20685__boxed_1527_ = lean_unbox(v___x_1511_);
v_res_1528_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_1509_, v_ident_1510_, v___x_20685__boxed_1527_, v_hyps_1512_, v___x_1513_, v_target_1514_, v_u_1515_, v_k_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v_s_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(lean_object* v_goal_1529_, lean_object* v_ident_1530_, lean_object* v_k_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___y_1542_; lean_object* v_u_1551_; lean_object* v_00_u03c3s_1552_; lean_object* v_hyps_1553_; lean_object* v_target_1554_; lean_object* v___x_1555_; 
v_u_1551_ = lean_ctor_get(v_goal_1529_, 0);
lean_inc(v_u_1551_);
v_00_u03c3s_1552_ = lean_ctor_get(v_goal_1529_, 1);
lean_inc_ref(v_00_u03c3s_1552_);
v_hyps_1553_ = lean_ctor_get(v_goal_1529_, 2);
lean_inc_ref(v_hyps_1553_);
v_target_1554_ = lean_ctor_get(v_goal_1529_, 3);
lean_inc_ref(v_target_1554_);
lean_dec_ref(v_goal_1529_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc_ref(v_00_u03c3s_1552_);
v___x_1555_ = lean_whnf(v_00_u03c3s_1552_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_1558_ = lean_unsigned_to_nat(3u);
v___x_1559_ = l_Lean_Expr_isAppOfArity(v_a_1556_, v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_a_1556_);
lean_dec_ref(v_target_1554_);
lean_dec_ref(v_hyps_1553_);
lean_dec(v_u_1551_);
lean_dec_ref(v_k_1531_);
lean_dec(v_ident_1530_);
v___x_1560_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_1561_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_1552_);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1562_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
v___y_1542_ = v___x_1563_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
lean_dec_ref(v_00_u03c3s_1552_);
v___x_1564_ = l_Lean_Expr_appFn_x21(v_a_1556_);
v___x_1565_ = l_Lean_Expr_appArg_x21(v___x_1564_);
lean_dec_ref(v___x_1564_);
v___x_1566_ = l_Lean_Expr_appArg_x21(v_a_1556_);
lean_dec(v_a_1556_);
v___x_1567_ = lean_box(v___x_1559_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
lean_inc(v_ident_1530_);
lean_inc_ref(v___x_1565_);
v___f_1568_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1568_, 0, v___x_1565_);
lean_closure_set(v___f_1568_, 1, v_ident_1530_);
lean_closure_set(v___f_1568_, 2, v___x_1567_);
lean_closure_set(v___f_1568_, 3, v_hyps_1553_);
lean_closure_set(v___f_1568_, 4, v___x_1566_);
lean_closure_set(v___f_1568_, 5, v_target_1554_);
lean_closure_set(v___f_1568_, 6, v_u_1551_);
lean_closure_set(v___f_1568_, 7, v_k_1531_);
lean_closure_set(v___f_1568_, 8, v___y_1532_);
lean_closure_set(v___f_1568_, 9, v___y_1533_);
lean_closure_set(v___f_1568_, 10, v___y_1534_);
lean_closure_set(v___f_1568_, 11, v___y_1535_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1530_);
v___x_1570_ = l_Lean_Syntax_isOfKind(v_ident_1530_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_ident_1530_);
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1572_ = l_Lean_Core_mkFreshUserName(v___x_1571_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1573_, v___x_1565_, v___f_1568_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
v___y_1542_ = v___x_1574_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v___f_1568_);
lean_dec_ref(v___x_1565_);
v_a_1575_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1572_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1572_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = l_Lean_Syntax_getArg(v_ident_1530_, v___x_1583_);
lean_dec(v_ident_1530_);
v___x_1585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_1584_);
v___x_1586_ = l_Lean_Syntax_isOfKind(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v___x_1584_);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1588_ = l_Lean_Core_mkFreshUserName(v___x_1587_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1589_, v___x_1565_, v___f_1568_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
v___y_1542_ = v___x_1590_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v___f_1568_);
lean_dec_ref(v___x_1565_);
v_a_1591_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1588_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1588_);
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
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = l_Lean_TSyntax_getId(v___x_1584_);
lean_dec(v___x_1584_);
v___x_1600_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v___x_1599_, v___x_1565_, v___f_1568_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
v___y_1542_ = v___x_1600_;
goto v___jp_1541_;
}
}
}
}
else
{
lean_dec_ref(v_target_1554_);
lean_dec_ref(v_hyps_1553_);
lean_dec_ref(v_00_u03c3s_1552_);
lean_dec(v_u_1551_);
lean_dec_ref(v_k_1531_);
lean_dec(v_ident_1530_);
return v___x_1555_;
}
v___jp_1541_:
{
if (lean_obj_tag(v___y_1542_) == 0)
{
return v___y_1542_;
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___y_1542_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___y_1542_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___y_1542_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___y_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(lean_object* v_goal_1601_, lean_object* v_ident_1602_, lean_object* v_k_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_1601_, v_ident_1602_, v_k_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(lean_object* v___x_1614_, lean_object* v_snd_1615_, lean_object* v_ident_1616_, lean_object* v_fst_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_st_mk_ref(v___x_1614_);
lean_inc(v___x_1627_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1628_, 0, v___x_1627_);
v___x_1629_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_snd_1615_, v_ident_1616_, v___f_1628_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref(v___x_1629_);
v___x_1631_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1617_, v_a_1630_, v___y_1623_);
lean_dec_ref(v___x_1631_);
v___x_1632_ = lean_st_ref_get(v___x_1627_);
lean_dec(v___x_1627_);
v___x_1633_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1632_, v___y_1619_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1633_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___x_1627_);
lean_dec(v_fst_1617_);
v_a_1634_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1629_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1629_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(lean_object* v___x_1642_, lean_object* v_snd_1643_, lean_object* v_ident_1644_, lean_object* v_fst_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(v___x_1642_, v_snd_1643_, v_ident_1644_, v_fst_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(lean_object* v_k_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v_b_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
v___x_1667_ = lean_apply_10(v_k_1656_, v_b_1661_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, lean_box(0));
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(lean_object* v_k_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v_b_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v_b_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(lean_object* v_name_1680_, lean_object* v_type_1681_, lean_object* v_val_1682_, lean_object* v_k_1683_, uint8_t v_nondep_1684_, uint8_t v_kind_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___f_1695_; lean_object* v___x_1696_; 
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1695_, 0, v_k_1683_);
lean_closure_set(v___f_1695_, 1, v___y_1686_);
lean_closure_set(v___f_1695_, 2, v___y_1687_);
lean_closure_set(v___f_1695_, 3, v___y_1688_);
lean_closure_set(v___f_1695_, 4, v___y_1689_);
v___x_1696_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1680_, v_type_1681_, v_val_1682_, v___f_1695_, v_nondep_1684_, v_kind_1685_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1696_) == 0)
{
return v___x_1696_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(lean_object* v_name_1705_, lean_object* v_type_1706_, lean_object* v_val_1707_, lean_object* v_k_1708_, lean_object* v_nondep_1709_, lean_object* v_kind_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v_nondep_boxed_1720_; uint8_t v_kind_boxed_1721_; lean_object* v_res_1722_; 
v_nondep_boxed_1720_ = lean_unbox(v_nondep_1709_);
v_kind_boxed_1721_ = lean_unbox(v_kind_1710_);
v_res_1722_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1705_, v_type_1706_, v_val_1707_, v_k_1708_, v_nondep_boxed_1720_, v_kind_boxed_1721_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v_ngen_1726_; lean_object* v_namePrefix_1727_; lean_object* v_idx_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1757_; 
v___x_1725_ = lean_st_ref_get(v___y_1723_);
v_ngen_1726_ = lean_ctor_get(v___x_1725_, 2);
lean_inc_ref(v_ngen_1726_);
lean_dec(v___x_1725_);
v_namePrefix_1727_ = lean_ctor_get(v_ngen_1726_, 0);
v_idx_1728_ = lean_ctor_get(v_ngen_1726_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_ngen_1726_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1730_ = v_ngen_1726_;
v_isShared_1731_ = v_isSharedCheck_1757_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_idx_1728_);
lean_inc(v_namePrefix_1727_);
lean_dec(v_ngen_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1757_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v_env_1733_; lean_object* v_nextMacroScope_1734_; lean_object* v_auxDeclNGen_1735_; lean_object* v_traceState_1736_; lean_object* v_cache_1737_; lean_object* v_messages_1738_; lean_object* v_infoState_1739_; lean_object* v_snapshotTasks_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1755_; 
v___x_1732_ = lean_st_ref_take(v___y_1723_);
v_env_1733_ = lean_ctor_get(v___x_1732_, 0);
v_nextMacroScope_1734_ = lean_ctor_get(v___x_1732_, 1);
v_auxDeclNGen_1735_ = lean_ctor_get(v___x_1732_, 3);
v_traceState_1736_ = lean_ctor_get(v___x_1732_, 4);
v_cache_1737_ = lean_ctor_get(v___x_1732_, 5);
v_messages_1738_ = lean_ctor_get(v___x_1732_, 6);
v_infoState_1739_ = lean_ctor_get(v___x_1732_, 7);
v_snapshotTasks_1740_ = lean_ctor_get(v___x_1732_, 8);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v___x_1732_, 2);
lean_dec(v_unused_1756_);
v___x_1742_ = v___x_1732_;
v_isShared_1743_ = v_isSharedCheck_1755_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snapshotTasks_1740_);
lean_inc(v_infoState_1739_);
lean_inc(v_messages_1738_);
lean_inc(v_cache_1737_);
lean_inc(v_traceState_1736_);
lean_inc(v_auxDeclNGen_1735_);
lean_inc(v_nextMacroScope_1734_);
lean_inc(v_env_1733_);
lean_dec(v___x_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1755_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_r_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
lean_inc(v_idx_1728_);
lean_inc(v_namePrefix_1727_);
v_r_1744_ = l_Lean_Name_num___override(v_namePrefix_1727_, v_idx_1728_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_add(v_idx_1728_, v___x_1745_);
lean_dec(v_idx_1728_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v___x_1746_);
v___x_1748_ = v___x_1730_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_namePrefix_1727_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 2, v___x_1748_);
v___x_1750_ = v___x_1742_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_env_1733_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_nextMacroScope_1734_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_auxDeclNGen_1735_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_traceState_1736_);
lean_ctor_set(v_reuseFailAlloc_1753_, 5, v_cache_1737_);
lean_ctor_set(v_reuseFailAlloc_1753_, 6, v_messages_1738_);
lean_ctor_set(v_reuseFailAlloc_1753_, 7, v_infoState_1739_);
lean_ctor_set(v_reuseFailAlloc_1753_, 8, v_snapshotTasks_1740_);
v___x_1750_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_st_ref_set(v___y_1723_, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_r_1744_);
return v___x_1752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1758_);
lean_dec(v___y_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(lean_object* v_body_1761_, lean_object* v_u_1762_, lean_object* v_00_u03c3s_1763_, lean_object* v_hyps_1764_, lean_object* v_k_1765_, lean_object* v_val_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = lean_expr_instantiate1(v_body_1761_, v_val_1766_);
v___x_1777_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1777_, 0, v_u_1762_);
lean_ctor_set(v___x_1777_, 1, v_00_u03c3s_1763_);
lean_ctor_set(v___x_1777_, 2, v_hyps_1764_);
lean_ctor_set(v___x_1777_, 3, v___x_1776_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
v___x_1778_ = lean_apply_10(v_k_1765_, v___x_1777_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, lean_box(0));
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_mk_empty_array_with_capacity(v___x_1780_);
v___x_1782_ = lean_array_push(v___x_1781_, v_val_1766_);
v___x_1783_ = 1;
v___x_1784_ = 1;
v___x_1785_ = l_Lean_Meta_mkLetFVars(v___x_1782_, v_a_1779_, v___x_1783_, v___x_1783_, v___x_1784_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec_ref(v___x_1782_);
return v___x_1785_;
}
else
{
lean_dec_ref(v_val_1766_);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(lean_object* v_body_1786_, lean_object* v_u_1787_, lean_object* v_00_u03c3s_1788_, lean_object* v_hyps_1789_, lean_object* v_k_1790_, lean_object* v_val_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_1786_, v_u_1787_, v_00_u03c3s_1788_, v_hyps_1789_, v_k_1790_, v_val_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_body_1786_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(lean_object* v_goal_1809_, lean_object* v_ident_1810_, lean_object* v_k_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_u_1821_; lean_object* v_00_u03c3s_1822_; lean_object* v_hyps_1823_; lean_object* v_target_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1935_; 
v_u_1821_ = lean_ctor_get(v_goal_1809_, 0);
v_00_u03c3s_1822_ = lean_ctor_get(v_goal_1809_, 1);
v_hyps_1823_ = lean_ctor_get(v_goal_1809_, 2);
v_target_1824_ = lean_ctor_get(v_goal_1809_, 3);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_goal_1809_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1826_ = v_goal_1809_;
v_isShared_1827_ = v_isSharedCheck_1935_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_target_1824_);
lean_inc(v_hyps_1823_);
lean_inc(v_00_u03c3s_1822_);
lean_inc(v_u_1821_);
lean_dec(v_goal_1809_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1935_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1828_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_1829_ = lean_unsigned_to_nat(3u);
v___x_1830_ = l_Lean_Expr_isAppOfArity(v_target_1824_, v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_del_object(v___x_1826_);
if (lean_obj_tag(v_target_1824_) == 8)
{
lean_object* v_declName_1831_; lean_object* v_type_1832_; lean_object* v_value_1833_; lean_object* v_body_1834_; lean_object* v___f_1835_; lean_object* v_name_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_declName_1831_ = lean_ctor_get(v_target_1824_, 0);
lean_inc(v_declName_1831_);
v_type_1832_ = lean_ctor_get(v_target_1824_, 1);
lean_inc_ref(v_type_1832_);
v_value_1833_ = lean_ctor_get(v_target_1824_, 2);
lean_inc_ref(v_value_1833_);
v_body_1834_ = lean_ctor_get(v_target_1824_, 3);
lean_inc_ref(v_body_1834_);
lean_dec_ref(v_target_1824_);
v___f_1835_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed), 15, 5);
lean_closure_set(v___f_1835_, 0, v_body_1834_);
lean_closure_set(v___f_1835_, 1, v_u_1821_);
lean_closure_set(v___f_1835_, 2, v_00_u03c3s_1822_);
lean_closure_set(v___f_1835_, 3, v_hyps_1823_);
lean_closure_set(v___f_1835_, 4, v_k_1811_);
v___x_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1810_);
v___x_1849_ = l_Lean_Syntax_isOfKind(v_ident_1810_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_dec(v_ident_1810_);
v___x_1850_ = l_Lean_Core_mkFreshUserName(v_declName_1831_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1850_);
v_name_1837_ = v_a_1851_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
v___y_1844_ = v___y_1818_;
v___y_1845_ = v___y_1819_;
goto v___jp_1836_;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v___f_1835_);
lean_dec_ref(v_value_1833_);
lean_dec_ref(v_type_1832_);
v_a_1852_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1850_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1850_);
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
else
{
lean_object* v___x_1860_; lean_object* v_name_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v_name_1861_ = l_Lean_Syntax_getArg(v_ident_1810_, v___x_1860_);
lean_dec(v_ident_1810_);
v___x_1862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_1861_);
v___x_1863_ = l_Lean_Syntax_isOfKind(v_name_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec(v_name_1861_);
v___x_1864_ = l_Lean_Core_mkFreshUserName(v_declName_1831_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v_name_1837_ = v_a_1865_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
v___y_1844_ = v___y_1818_;
v___y_1845_ = v___y_1819_;
goto v___jp_1836_;
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v___f_1835_);
lean_dec_ref(v_value_1833_);
lean_dec_ref(v_type_1832_);
v_a_1866_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1864_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1864_);
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
else
{
lean_object* v___x_1874_; 
lean_dec(v_declName_1831_);
v___x_1874_ = l_Lean_TSyntax_getId(v_name_1861_);
lean_dec(v_name_1861_);
v_name_1837_ = v___x_1874_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
v___y_1844_ = v___y_1818_;
v___y_1845_ = v___y_1819_;
goto v___jp_1836_;
}
}
v___jp_1836_:
{
uint8_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = 0;
v___x_1847_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1837_, v_type_1832_, v_value_1833_, v___f_1835_, v___x_1830_, v___x_1846_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1847_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v_hyps_1823_);
lean_dec_ref(v_00_u03c3s_1822_);
lean_dec(v_u_1821_);
lean_dec_ref(v_k_1811_);
lean_dec(v_ident_1810_);
v___x_1875_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_1876_ = l_Lean_MessageData_ofExpr(v_target_1824_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1877_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1878_;
}
}
else
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_1810_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_hyp_1889_; lean_object* v___x_1890_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1879_);
v_fst_1881_ = lean_ctor_get(v_a_1880_, 0);
lean_inc(v_fst_1881_);
v_snd_1882_ = lean_ctor_get(v_a_1880_, 1);
lean_inc(v_snd_1882_);
lean_dec(v_a_1880_);
v___x_1883_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1819_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_Expr_appFn_x21(v_target_1824_);
v___x_1886_ = l_Lean_Expr_appFn_x21(v___x_1885_);
v___x_1887_ = l_Lean_Expr_appArg_x21(v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = l_Lean_Expr_appArg_x21(v___x_1885_);
lean_dec_ref(v___x_1885_);
v_hyp_1889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_1889_, 0, v_fst_1881_);
lean_ctor_set(v_hyp_1889_, 1, v_a_1884_);
lean_ctor_set(v_hyp_1889_, 2, v___x_1888_);
lean_inc_ref(v___y_1816_);
lean_inc_ref(v_hyp_1889_);
lean_inc_ref(v___x_1887_);
v___x_1890_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1882_, v___x_1887_, v_hyp_1889_, v___x_1830_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_H_1891_; lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v___x_1890_);
v_H_1891_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_1889_);
lean_inc_ref(v_H_1891_);
lean_inc_ref(v_hyps_1823_);
lean_inc_ref(v_00_u03c3s_1822_);
lean_inc(v_u_1821_);
v___x_1892_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_1821_, v_00_u03c3s_1822_, v_hyps_1823_, v_H_1891_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1896_ = v___x_1892_;
v_isShared_1897_ = v_isSharedCheck_1918_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snd_1894_);
lean_inc(v_fst_1893_);
lean_dec(v___x_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1918_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = l_Lean_Expr_appArg_x21(v_target_1824_);
lean_dec_ref(v_target_1824_);
lean_inc_ref(v___x_1898_);
lean_inc(v_fst_1893_);
lean_inc(v_u_1821_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 3, v___x_1898_);
lean_ctor_set(v___x_1826_, 2, v_fst_1893_);
v___x_1900_ = v___x_1826_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_u_1821_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_00_u03c3s_1822_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_fst_1893_);
lean_ctor_set(v_reuseFailAlloc_1917_, 3, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; 
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
v___x_1901_ = lean_apply_10(v_k_1811_, v___x_1900_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, lean_box(0));
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1916_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1916_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1916_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0));
v___x_1907_ = lean_box(0);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 1);
lean_ctor_set(v___x_1896_, 1, v___x_1907_);
lean_ctor_set(v___x_1896_, 0, v_u_1821_);
v___x_1909_ = v___x_1896_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_u_1821_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v_prf_1911_; lean_object* v___x_1913_; 
v___x_1910_ = l_Lean_mkConst(v___x_1906_, v___x_1909_);
v_prf_1911_ = l_Lean_mkApp7(v___x_1910_, v___x_1887_, v_fst_1893_, v_hyps_1823_, v_H_1891_, v___x_1898_, v_snd_1894_, v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_prf_1911_);
v___x_1913_ = v___x_1904_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_prf_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_dec_ref(v___x_1898_);
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec_ref(v_H_1891_);
lean_dec_ref(v___x_1887_);
lean_dec_ref(v_hyps_1823_);
lean_dec(v_u_1821_);
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_hyp_1889_);
lean_dec_ref(v___x_1887_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_target_1824_);
lean_dec_ref(v_hyps_1823_);
lean_dec_ref(v_00_u03c3s_1822_);
lean_dec(v_u_1821_);
lean_dec_ref(v_k_1811_);
v_a_1919_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1890_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1890_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_del_object(v___x_1826_);
lean_dec_ref(v_target_1824_);
lean_dec_ref(v_hyps_1823_);
lean_dec_ref(v_00_u03c3s_1822_);
lean_dec(v_u_1821_);
lean_dec_ref(v_k_1811_);
v_a_1927_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1879_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1879_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(lean_object* v_goal_1936_, lean_object* v_ident_1937_, lean_object* v_k_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_1936_, v_ident_1937_, v_k_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(lean_object* v___x_1949_, lean_object* v_snd_1950_, lean_object* v_ident_1951_, lean_object* v_fst_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_st_mk_ref(v___x_1949_);
lean_inc(v___x_1962_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1963_, 0, v___x_1962_);
v___x_1964_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_snd_1950_, v_ident_1951_, v___f_1963_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
v___x_1966_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1952_, v_a_1965_, v___y_1958_);
lean_dec_ref(v___x_1966_);
v___x_1967_ = lean_st_ref_get(v___x_1962_);
lean_dec(v___x_1962_);
v___x_1968_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1967_, v___y_1954_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1968_;
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v___x_1962_);
lean_dec(v_fst_1952_);
v_a_1969_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1964_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1964_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed(lean_object* v___x_1977_, lean_object* v_snd_1978_, lean_object* v_ident_1979_, lean_object* v_fst_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(v___x_1977_, v_snd_1978_, v_ident_1979_, v_fst_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(lean_object* v_x_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_1997_);
v___x_2008_ = l_Lean_Syntax_isOfKind(v_x_1997_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_x_1997_);
v___x_2009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = l_Lean_Syntax_getArg(v_x_1997_, v___x_2010_);
lean_dec(v_x_1997_);
lean_inc(v___x_2011_);
v___x_2012_ = l_Lean_Syntax_matchesNull(v___x_2011_, v___x_2010_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
lean_dec(v___x_2011_);
v___x_2013_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = l_Lean_Syntax_getArg(v___x_2011_, v___x_2014_);
lean_dec(v___x_2011_);
v___x_2016_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_2015_);
v___x_2017_ = l_Lean_Syntax_isOfKind(v___x_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1));
lean_inc(v___x_2015_);
v___x_2019_ = l_Lean_Syntax_isOfKind(v___x_2015_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v___x_2015_);
v___x_2020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2020_;
}
else
{
lean_object* v_ident_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_ident_2021_ = l_Lean_Syntax_getArg(v___x_2015_, v___x_2010_);
lean_dec(v___x_2015_);
v___x_2022_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_2021_);
v___x_2023_ = l_Lean_Syntax_isOfKind(v_ident_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec(v_ident_2021_);
v___x_2024_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1999_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___x_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2025_);
v_fst_2027_ = lean_ctor_get(v_a_2026_, 0);
lean_inc(v_fst_2027_);
v_snd_2028_ = lean_ctor_get(v_a_2026_, 1);
lean_inc(v_snd_2028_);
lean_dec(v_a_2026_);
v___x_2029_ = lean_box(0);
lean_inc(v_fst_2027_);
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2030_, 0, v___x_2029_);
lean_closure_set(v___f_2030_, 1, v_snd_2028_);
lean_closure_set(v___f_2030_, 2, v_ident_2021_);
lean_closure_set(v___f_2030_, 3, v_fst_2027_);
v___x_2031_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2027_, v___f_2030_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
return v___x_2031_;
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_ident_2021_);
v_a_2032_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2025_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2025_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2040_ = l_Lean_Syntax_getArg(v___x_2015_, v___x_2014_);
lean_dec(v___x_2015_);
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_2040_);
v___x_2042_ = l_Lean_Syntax_isOfKind(v___x_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
lean_dec(v___x_2040_);
v___x_2043_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2043_;
}
else
{
lean_object* v_ident_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_ident_2044_ = l_Lean_Syntax_getArg(v___x_2040_, v___x_2014_);
lean_dec(v___x_2040_);
v___x_2045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_2044_);
v___x_2046_ = l_Lean_Syntax_isOfKind(v_ident_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_dec(v_ident_2044_);
v___x_2047_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1999_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v_fst_2050_ = lean_ctor_get(v_a_2049_, 0);
lean_inc(v_fst_2050_);
v_snd_2051_ = lean_ctor_get(v_a_2049_, 1);
lean_inc(v_snd_2051_);
lean_dec(v_a_2049_);
v___x_2052_ = lean_box(0);
lean_inc(v_fst_2050_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2053_, 0, v___x_2052_);
lean_closure_set(v___f_2053_, 1, v_snd_2051_);
lean_closure_set(v___f_2053_, 2, v_ident_2044_);
lean_closure_set(v___f_2053_, 3, v_fst_2050_);
v___x_2054_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2050_, v___f_2053_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
return v___x_2054_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_ident_2044_);
v_a_2055_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2048_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2048_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(lean_object* v_x_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(v_x_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(lean_object* v_mvarId_2074_, lean_object* v_val_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_2074_, v_val_2075_, v___y_2081_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(lean_object* v_mvarId_2086_, lean_object* v_val_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(v_mvarId_2086_, v_val_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_object* v_00_u03b1_2098_, lean_object* v_name_2099_, lean_object* v_type_2100_, lean_object* v_val_2101_, lean_object* v_k_2102_, uint8_t v_nondep_2103_, uint8_t v_kind_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_2099_, v_type_2100_, v_val_2101_, v_k_2102_, v_nondep_2103_, v_kind_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2115_, lean_object* v_name_2116_, lean_object* v_type_2117_, lean_object* v_val_2118_, lean_object* v_k_2119_, lean_object* v_nondep_2120_, lean_object* v_kind_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v_nondep_boxed_2131_; uint8_t v_kind_boxed_2132_; lean_object* v_res_2133_; 
v_nondep_boxed_2131_ = lean_unbox(v_nondep_2120_);
v_kind_boxed_2132_ = lean_unbox(v_kind_2121_);
v_res_2133_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(v_00_u03b1_2115_, v_name_2116_, v_type_2117_, v_val_2118_, v_k_2119_, v_nondep_boxed_2131_, v_kind_boxed_2132_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_object* v_00_u03b1_2146_, lean_object* v_msg_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(v_00_u03b1_2154_, v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2162_, lean_object* v_name_2163_, uint8_t v_bi_2164_, lean_object* v_type_2165_, lean_object* v_k_2166_, uint8_t v_kind_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_2163_, v_bi_2164_, v_type_2165_, v_k_2166_, v_kind_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2174_, lean_object* v_name_2175_, lean_object* v_bi_2176_, lean_object* v_type_2177_, lean_object* v_k_2178_, lean_object* v_kind_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
uint8_t v_bi_boxed_2185_; uint8_t v_kind_boxed_2186_; lean_object* v_res_2187_; 
v_bi_boxed_2185_ = lean_unbox(v_bi_2176_);
v_kind_boxed_2186_ = lean_unbox(v_kind_2179_);
v_res_2187_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(v_00_u03b1_2174_, v_name_2175_, v_bi_boxed_2185_, v_type_2177_, v_k_2178_, v_kind_boxed_2186_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_object* v_00_u03b1_2188_, lean_object* v_name_2189_, lean_object* v_type_2190_, lean_object* v_k_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_2189_, v_type_2190_, v_k_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_name_2199_, lean_object* v_type_2200_, lean_object* v_k_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(v_00_u03b1_2198_, v_name_2199_, v_type_2200_, v_k_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(lean_object* v_00_u03b2_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_x_2209_, v_x_2210_, v_x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2213_, lean_object* v_x_2214_, size_t v_x_2215_, size_t v_x_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_2214_, v_x_2215_, v_x_2216_, v_x_2217_, v_x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
size_t v_x_21863__boxed_2226_; size_t v_x_21864__boxed_2227_; lean_object* v_res_2228_; 
v_x_21863__boxed_2226_ = lean_unbox_usize(v_x_2222_);
lean_dec(v_x_2222_);
v_x_21864__boxed_2227_ = lean_unbox_usize(v_x_2223_);
lean_dec(v_x_2223_);
v_res_2228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(v_00_u03b2_2220_, v_x_2221_, v_x_21863__boxed_2226_, v_x_21864__boxed_2227_, v_x_2224_, v_x_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2229_, lean_object* v_n_2230_, lean_object* v_k_2231_, lean_object* v_v_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v_n_2230_, v_k_2231_, v_v_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b2_2234_, size_t v_depth_2235_, lean_object* v_keys_2236_, lean_object* v_vals_2237_, lean_object* v_heq_2238_, lean_object* v_i_2239_, lean_object* v_entries_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_2235_, v_keys_2236_, v_vals_2237_, v_i_2239_, v_entries_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_depth_2243_, lean_object* v_keys_2244_, lean_object* v_vals_2245_, lean_object* v_heq_2246_, lean_object* v_i_2247_, lean_object* v_entries_2248_){
_start:
{
size_t v_depth_boxed_2249_; lean_object* v_res_2250_; 
v_depth_boxed_2249_ = lean_unbox_usize(v_depth_2243_);
lean_dec(v_depth_2243_);
v_res_2250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(v_00_u03b2_2242_, v_depth_boxed_2249_, v_keys_2244_, v_vals_2245_, v_heq_2246_, v_i_2247_, v_entries_2248_);
lean_dec_ref(v_vals_2245_);
lean_dec_ref(v_keys_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_x_2252_, v_x_2253_, v_x_2254_, v_x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1(){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2268_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2269_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_2270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3));
v___x_2271_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed), 10, 0);
v___x_2272_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2268_, v___x_2269_, v___x_2270_, v___x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
return v_res_2274_;
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
