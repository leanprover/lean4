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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_type_38_, lean_object* v_value_39_, lean_object* v___f_40_, uint8_t v___x_41_, lean_object* v_name_42_){
_start:
{
uint8_t v___x_43_; lean_object* v___x_44_; 
v___x_43_ = 0;
v___x_44_ = l_Lean_Meta_withLetDecl___redArg(v_inst_36_, v_inst_37_, v_name_42_, v_type_38_, v_value_39_, v___f_40_, v___x_41_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_36_ = stack[0].m_obj;
lean_object* v_inst_37_ = stack[1].m_obj;
lean_object* v_type_38_ = stack[2].m_obj;
lean_object* v_value_39_ = stack[3].m_obj;
lean_object* v___f_40_ = stack[4].m_obj;
uint8_t v___x_41_ = stack[5].m_num;
lean_object* v_name_42_ = stack[6].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(v_inst_36_, v_inst_37_, v_type_38_, v_value_39_, v___f_40_, v___x_41_, v_name_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed(lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_type_48_, lean_object* v_value_49_, lean_object* v___f_50_, lean_object* v___x_51_, lean_object* v_name_52_){
_start:
{
uint8_t v___x_1247__boxed_53_; lean_object* v_res_54_; 
v___x_1247__boxed_53_ = lean_unbox(v___x_51_);
v_res_54_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(v_inst_46_, v_inst_47_, v_type_48_, v_value_49_, v___f_50_, v___x_1247__boxed_53_, v_name_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3(lean_object* v___f_55_, lean_object* v_name_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_apply_1(v___f_55_, v_name_56_);
return v___x_57_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(lean_object* v_declName_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Core_mkFreshUserName(v_declName_58_, v___y_61_, v___y_62_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_58_ = stack[0].m_obj;
lean_object* v___y_59_ = stack[1].m_obj;
lean_object* v___y_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(v_declName_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed(lean_object* v_declName_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(v_declName_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_72_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(lean_object* v_ident_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_73_, v___y_76_, v___y_77_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ident_73_ = stack[0].m_obj;
lean_object* v___y_74_ = stack[1].m_obj;
lean_object* v___y_75_ = stack[2].m_obj;
lean_object* v___y_76_ = stack[3].m_obj;
lean_object* v___y_77_ = stack[4].m_obj;
lean_object* v_res_80_;
v_res_80_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(v_ident_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed(lean_object* v_ident_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(v_ident_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5(lean_object* v___x_91_, lean_object* v___x_92_, lean_object* v___x_93_, lean_object* v_u_94_, lean_object* v___x_95_, lean_object* v_fst_96_, lean_object* v_hyps_97_, lean_object* v_H_98_, lean_object* v___x_99_, lean_object* v_snd_100_, lean_object* v_toPure_101_, lean_object* v_prf_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_prf_110_; lean_object* v___x_111_; 
v___x_103_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0));
v___x_104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1));
v___x_105_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2));
v___x_106_ = l_Lean_Name_mkStr6(v___x_91_, v___x_92_, v___x_93_, v___x_103_, v___x_104_, v___x_105_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v_u_94_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = l_Lean_mkConst(v___x_106_, v___x_108_);
v_prf_110_ = l_Lean_mkApp7(v___x_109_, v___x_95_, v_fst_96_, v_hyps_97_, v_H_98_, v___x_99_, v_snd_100_, v_prf_102_);
v___x_111_ = lean_apply_2(v_toPure_101_, lean_box(0), v_prf_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6(lean_object* v_hyp_112_, lean_object* v_u_113_, lean_object* v_00_u03c3s_114_, lean_object* v_hyps_115_, lean_object* v___x_116_, lean_object* v___x_117_, lean_object* v___x_118_, lean_object* v___x_119_, lean_object* v___x_120_, lean_object* v_toPure_121_, lean_object* v_k_122_, lean_object* v_toBind_123_, lean_object* v_____r_124_){
_start:
{
lean_object* v_H_125_; lean_object* v___x_126_; lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_H_125_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_112_);
lean_inc_ref(v_H_125_);
lean_inc_ref(v_hyps_115_);
lean_inc_ref(v_00_u03c3s_114_);
lean_inc_n(v_u_113_, 2);
v___x_126_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_113_, v_00_u03c3s_114_, v_hyps_115_, v_H_125_);
v_fst_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_n(v_fst_127_, 2);
v_snd_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_snd_128_);
lean_dec_ref(v___x_126_);
lean_inc_ref(v___x_120_);
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5), 12, 11);
lean_closure_set(v___f_129_, 0, v___x_116_);
lean_closure_set(v___f_129_, 1, v___x_117_);
lean_closure_set(v___f_129_, 2, v___x_118_);
lean_closure_set(v___f_129_, 3, v_u_113_);
lean_closure_set(v___f_129_, 4, v___x_119_);
lean_closure_set(v___f_129_, 5, v_fst_127_);
lean_closure_set(v___f_129_, 6, v_hyps_115_);
lean_closure_set(v___f_129_, 7, v_H_125_);
lean_closure_set(v___f_129_, 8, v___x_120_);
lean_closure_set(v___f_129_, 9, v_snd_128_);
lean_closure_set(v___f_129_, 10, v_toPure_121_);
v___x_130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_130_, 0, v_u_113_);
lean_ctor_set(v___x_130_, 1, v_00_u03c3s_114_);
lean_ctor_set(v___x_130_, 2, v_fst_127_);
lean_ctor_set(v___x_130_, 3, v___x_120_);
v___x_131_ = lean_apply_1(v_k_122_, v___x_130_);
v___x_132_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_131_, v___f_129_);
return v___x_132_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(lean_object* v_fst_133_, lean_object* v___x_134_, lean_object* v_u_135_, lean_object* v_00_u03c3s_136_, lean_object* v_hyps_137_, lean_object* v___x_138_, lean_object* v___x_139_, lean_object* v___x_140_, lean_object* v___x_141_, lean_object* v___x_142_, lean_object* v_toPure_143_, lean_object* v_k_144_, lean_object* v_toBind_145_, lean_object* v_snd_146_, uint8_t v___x_147_, lean_object* v_inst_148_, lean_object* v_uniq_149_){
_start:
{
lean_object* v_hyp_150_; lean_object* v___f_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_hyp_150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_150_, 0, v_fst_133_);
lean_ctor_set(v_hyp_150_, 1, v_uniq_149_);
lean_ctor_set(v_hyp_150_, 2, v___x_134_);
lean_inc(v_toBind_145_);
lean_inc_ref(v___x_141_);
lean_inc_ref(v_hyp_150_);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6), 13, 12);
lean_closure_set(v___f_151_, 0, v_hyp_150_);
lean_closure_set(v___f_151_, 1, v_u_135_);
lean_closure_set(v___f_151_, 2, v_00_u03c3s_136_);
lean_closure_set(v___f_151_, 3, v_hyps_137_);
lean_closure_set(v___f_151_, 4, v___x_138_);
lean_closure_set(v___f_151_, 5, v___x_139_);
lean_closure_set(v___f_151_, 6, v___x_140_);
lean_closure_set(v___f_151_, 7, v___x_141_);
lean_closure_set(v___f_151_, 8, v___x_142_);
lean_closure_set(v___f_151_, 9, v_toPure_143_);
lean_closure_set(v___f_151_, 10, v_k_144_);
lean_closure_set(v___f_151_, 11, v_toBind_145_);
v___x_152_ = lean_box(v___x_147_);
v___x_153_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed), 9, 4);
lean_closure_set(v___x_153_, 0, v_snd_146_);
lean_closure_set(v___x_153_, 1, v___x_141_);
lean_closure_set(v___x_153_, 2, v_hyp_150_);
lean_closure_set(v___x_153_, 3, v___x_152_);
v___x_154_ = lean_apply_2(v_inst_148_, lean_box(0), v___x_153_);
v___x_155_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v___x_154_, v___f_151_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_133_ = stack[0].m_obj;
lean_object* v___x_134_ = stack[1].m_obj;
lean_object* v_u_135_ = stack[2].m_obj;
lean_object* v_00_u03c3s_136_ = stack[3].m_obj;
lean_object* v_hyps_137_ = stack[4].m_obj;
lean_object* v___x_138_ = stack[5].m_obj;
lean_object* v___x_139_ = stack[6].m_obj;
lean_object* v___x_140_ = stack[7].m_obj;
lean_object* v___x_141_ = stack[8].m_obj;
lean_object* v___x_142_ = stack[9].m_obj;
lean_object* v_toPure_143_ = stack[10].m_obj;
lean_object* v_k_144_ = stack[11].m_obj;
lean_object* v_toBind_145_ = stack[12].m_obj;
lean_object* v_snd_146_ = stack[13].m_obj;
uint8_t v___x_147_ = stack[14].m_num;
lean_object* v_inst_148_ = stack[15].m_obj;
lean_object* v_uniq_149_ = stack[16].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(v_fst_133_, v___x_134_, v_u_135_, v_00_u03c3s_136_, v_hyps_137_, v___x_138_, v___x_139_, v___x_140_, v___x_141_, v___x_142_, v_toPure_143_, v_k_144_, v_toBind_145_, v_snd_146_, v___x_147_, v_inst_148_, v_uniq_149_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_fst_157_ = _args[0];
lean_object* v___x_158_ = _args[1];
lean_object* v_u_159_ = _args[2];
lean_object* v_00_u03c3s_160_ = _args[3];
lean_object* v_hyps_161_ = _args[4];
lean_object* v___x_162_ = _args[5];
lean_object* v___x_163_ = _args[6];
lean_object* v___x_164_ = _args[7];
lean_object* v___x_165_ = _args[8];
lean_object* v___x_166_ = _args[9];
lean_object* v_toPure_167_ = _args[10];
lean_object* v_k_168_ = _args[11];
lean_object* v_toBind_169_ = _args[12];
lean_object* v_snd_170_ = _args[13];
lean_object* v___x_171_ = _args[14];
lean_object* v_inst_172_ = _args[15];
lean_object* v_uniq_173_ = _args[16];
_start:
{
uint8_t v___x_1449__boxed_174_; lean_object* v_res_175_; 
v___x_1449__boxed_174_ = lean_unbox(v___x_171_);
v_res_175_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(v_fst_157_, v___x_158_, v_u_159_, v_00_u03c3s_160_, v_hyps_161_, v___x_162_, v___x_163_, v___x_164_, v___x_165_, v___x_166_, v_toPure_167_, v_k_168_, v_toBind_169_, v_snd_170_, v___x_1449__boxed_174_, v_inst_172_, v_uniq_173_);
return v_res_175_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(lean_object* v___x_176_, lean_object* v_u_177_, lean_object* v_00_u03c3s_178_, lean_object* v_hyps_179_, lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v___x_182_, lean_object* v___x_183_, lean_object* v___x_184_, lean_object* v_toPure_185_, lean_object* v_k_186_, lean_object* v_toBind_187_, uint8_t v___x_188_, lean_object* v_inst_189_, lean_object* v___x_190_, lean_object* v___x_191_, lean_object* v_____x_192_){
_start:
{
lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v___x_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_fst_193_ = lean_ctor_get(v_____x_192_, 0);
lean_inc(v_fst_193_);
v_snd_194_ = lean_ctor_get(v_____x_192_, 1);
lean_inc(v_snd_194_);
lean_dec_ref(v_____x_192_);
v___x_195_ = lean_box(v___x_188_);
lean_inc(v_inst_189_);
lean_inc(v_toBind_187_);
v___f_196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_196_, 0, v_fst_193_);
lean_closure_set(v___f_196_, 1, v___x_176_);
lean_closure_set(v___f_196_, 2, v_u_177_);
lean_closure_set(v___f_196_, 3, v_00_u03c3s_178_);
lean_closure_set(v___f_196_, 4, v_hyps_179_);
lean_closure_set(v___f_196_, 5, v___x_180_);
lean_closure_set(v___f_196_, 6, v___x_181_);
lean_closure_set(v___f_196_, 7, v___x_182_);
lean_closure_set(v___f_196_, 8, v___x_183_);
lean_closure_set(v___f_196_, 9, v___x_184_);
lean_closure_set(v___f_196_, 10, v_toPure_185_);
lean_closure_set(v___f_196_, 11, v_k_186_);
lean_closure_set(v___f_196_, 12, v_toBind_187_);
lean_closure_set(v___f_196_, 13, v_snd_194_);
lean_closure_set(v___f_196_, 14, v___x_195_);
lean_closure_set(v___f_196_, 15, v_inst_189_);
v___x_197_ = l_Lean_mkFreshId___redArg(v___x_190_, v___x_191_);
v___x_198_ = lean_apply_2(v_inst_189_, lean_box(0), v___x_197_);
v___x_199_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_198_, v___f_196_);
return v___x_199_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_176_ = stack[0].m_obj;
lean_object* v_u_177_ = stack[1].m_obj;
lean_object* v_00_u03c3s_178_ = stack[2].m_obj;
lean_object* v_hyps_179_ = stack[3].m_obj;
lean_object* v___x_180_ = stack[4].m_obj;
lean_object* v___x_181_ = stack[5].m_obj;
lean_object* v___x_182_ = stack[6].m_obj;
lean_object* v___x_183_ = stack[7].m_obj;
lean_object* v___x_184_ = stack[8].m_obj;
lean_object* v_toPure_185_ = stack[9].m_obj;
lean_object* v_k_186_ = stack[10].m_obj;
lean_object* v_toBind_187_ = stack[11].m_obj;
uint8_t v___x_188_ = stack[12].m_num;
lean_object* v_inst_189_ = stack[13].m_obj;
lean_object* v___x_190_ = stack[14].m_obj;
lean_object* v___x_191_ = stack[15].m_obj;
lean_object* v_____x_192_ = stack[16].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(v___x_176_, v_u_177_, v_00_u03c3s_178_, v_hyps_179_, v___x_180_, v___x_181_, v___x_182_, v___x_183_, v___x_184_, v_toPure_185_, v_k_186_, v_toBind_187_, v___x_188_, v_inst_189_, v___x_190_, v___x_191_, v_____x_192_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed(lean_object** _args){
lean_object* v___x_201_ = _args[0];
lean_object* v_u_202_ = _args[1];
lean_object* v_00_u03c3s_203_ = _args[2];
lean_object* v_hyps_204_ = _args[3];
lean_object* v___x_205_ = _args[4];
lean_object* v___x_206_ = _args[5];
lean_object* v___x_207_ = _args[6];
lean_object* v___x_208_ = _args[7];
lean_object* v___x_209_ = _args[8];
lean_object* v_toPure_210_ = _args[9];
lean_object* v_k_211_ = _args[10];
lean_object* v_toBind_212_ = _args[11];
lean_object* v___x_213_ = _args[12];
lean_object* v_inst_214_ = _args[13];
lean_object* v___x_215_ = _args[14];
lean_object* v___x_216_ = _args[15];
lean_object* v_____x_217_ = _args[16];
_start:
{
uint8_t v___x_1512__boxed_218_; lean_object* v_res_219_; 
v___x_1512__boxed_218_ = lean_unbox(v___x_213_);
v_res_219_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(v___x_201_, v_u_202_, v_00_u03c3s_203_, v_hyps_204_, v___x_205_, v___x_206_, v___x_207_, v___x_208_, v___x_209_, v_toPure_210_, v_k_211_, v_toBind_212_, v___x_1512__boxed_218_, v_inst_214_, v___x_215_, v___x_216_, v_____x_217_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_instMonadEIO___redArg();
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0);
v___x_222_ = l_StateRefT_x27_instMonad___redArg(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_230_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5));
v___x_231_ = l_Lean_monadNameGeneratorLift___redArg(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9(void){
_start:
{
lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8);
v___f_233_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4));
v___x_234_ = l_Lean_monadNameGeneratorLift___redArg(v___f_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10(void){
_start:
{
lean_object* v___x_235_; lean_object* v___f_236_; 
v___x_235_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_236_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_236_, 0, v___x_235_);
return v___f_236_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11(void){
_start:
{
lean_object* v___x_237_; lean_object* v___f_238_; 
v___x_237_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_238_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_238_, 0, v___x_237_);
return v___f_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12(void){
_start:
{
lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; 
v___f_239_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11);
v___f_240_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___f_240_);
lean_ctor_set(v___x_241_, 1, v___f_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13(void){
_start:
{
lean_object* v___x_242_; lean_object* v___f_243_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12);
v___f_243_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_243_, 0, v___x_242_);
return v___f_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14(void){
_start:
{
lean_object* v___x_244_; lean_object* v___f_245_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12);
v___f_245_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_245_, 0, v___x_244_);
return v___f_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15(void){
_start:
{
lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_248_; 
v___f_246_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14);
v___f_247_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___f_247_);
lean_ctor_set(v___x_248_, 1, v___f_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5));
v___x_253_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17));
v___x_254_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_253_, v___x_252_, v___x_251_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19(void){
_start:
{
lean_object* v___x_255_; lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___x_258_; 
v___x_255_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18);
v___f_256_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4));
v___f_257_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16));
v___x_258_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_257_, v___f_256_, v___x_255_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_goal_282_, lean_object* v_ident_283_, lean_object* v_k_284_){
_start:
{
lean_object* v___x_285_; lean_object* v_toApplicative_286_; lean_object* v_toFunctor_287_; lean_object* v_toSeq_288_; lean_object* v_toSeqLeft_289_; lean_object* v_toSeqRight_290_; lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___f_293_; lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_toApplicative_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_397_; 
v___x_285_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_286_ = lean_ctor_get(v___x_285_, 0);
v_toFunctor_287_ = lean_ctor_get(v_toApplicative_286_, 0);
v_toSeq_288_ = lean_ctor_get(v_toApplicative_286_, 2);
v_toSeqLeft_289_ = lean_ctor_get(v_toApplicative_286_, 3);
v_toSeqRight_290_ = lean_ctor_get(v_toApplicative_286_, 4);
v___f_291_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_292_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_287_, 2);
v___f_293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_293_, 0, v_toFunctor_287_);
v___f_294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_294_, 0, v_toFunctor_287_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___f_293_);
lean_ctor_set(v___x_295_, 1, v___f_294_);
lean_inc(v_toSeqRight_290_);
v___f_296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_296_, 0, v_toSeqRight_290_);
lean_inc(v_toSeqLeft_289_);
v___f_297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_297_, 0, v_toSeqLeft_289_);
lean_inc(v_toSeq_288_);
v___f_298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_298_, 0, v_toSeq_288_);
v___x_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_299_, 0, v___x_295_);
lean_ctor_set(v___x_299_, 1, v___f_291_);
lean_ctor_set(v___x_299_, 2, v___f_298_);
lean_ctor_set(v___x_299_, 3, v___f_297_);
lean_ctor_set(v___x_299_, 4, v___f_296_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___f_292_);
v___x_301_ = l_StateRefT_x27_instMonad___redArg(v___x_300_);
v_toApplicative_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_301_, 1);
lean_dec(v_unused_398_);
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_397_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_toApplicative_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_397_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_toFunctor_306_; lean_object* v_toSeq_307_; lean_object* v_toSeqLeft_308_; lean_object* v_toSeqRight_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_395_; 
v_toFunctor_306_ = lean_ctor_get(v_toApplicative_302_, 0);
v_toSeq_307_ = lean_ctor_get(v_toApplicative_302_, 2);
v_toSeqLeft_308_ = lean_ctor_get(v_toApplicative_302_, 3);
v_toSeqRight_309_ = lean_ctor_get(v_toApplicative_302_, 4);
v_isSharedCheck_395_ = !lean_is_exclusive(v_toApplicative_302_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v_toApplicative_302_, 1);
lean_dec(v_unused_396_);
v___x_311_ = v_toApplicative_302_;
v_isShared_312_ = v_isSharedCheck_395_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_toSeqRight_309_);
lean_inc(v_toSeqLeft_308_);
lean_inc(v_toSeq_307_);
lean_inc(v_toFunctor_306_);
lean_dec(v_toApplicative_302_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_395_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___x_322_; 
v___f_313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_314_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_306_);
v___f_315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_315_, 0, v_toFunctor_306_);
v___f_316_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_316_, 0, v_toFunctor_306_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___f_315_);
lean_ctor_set(v___x_317_, 1, v___f_316_);
v___f_318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_318_, 0, v_toSeqRight_309_);
v___f_319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_319_, 0, v_toSeqLeft_308_);
v___f_320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_320_, 0, v_toSeq_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v___f_318_);
lean_ctor_set(v___x_311_, 3, v___f_319_);
lean_ctor_set(v___x_311_, 2, v___f_320_);
lean_ctor_set(v___x_311_, 1, v___f_313_);
lean_ctor_set(v___x_311_, 0, v___x_317_);
v___x_322_ = v___x_311_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___f_313_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v___f_320_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v___f_319_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v___f_318_);
v___x_322_ = v_reuseFailAlloc_394_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___f_314_);
lean_ctor_set(v___x_304_, 0, v___x_322_);
v___x_324_ = v___x_304_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___f_314_);
v___x_324_ = v_reuseFailAlloc_393_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_toMonadRef_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_toApplicative_332_; lean_object* v_toBind_333_; lean_object* v_toPure_334_; lean_object* v_u_335_; lean_object* v_00_u03c3s_336_; lean_object* v_hyps_337_; lean_object* v_target_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_325_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9);
v___x_326_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_327_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19);
v_toMonadRef_328_ = lean_ctor_get(v___x_327_, 0);
v___x_329_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_324_);
v___x_330_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_329_, v___x_324_);
lean_inc_ref(v_toMonadRef_328_);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v___x_326_);
lean_ctor_set(v___x_331_, 1, v_toMonadRef_328_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
v_toApplicative_332_ = lean_ctor_get(v_inst_279_, 0);
v_toBind_333_ = lean_ctor_get(v_inst_279_, 1);
v_toPure_334_ = lean_ctor_get(v_toApplicative_332_, 1);
v_u_335_ = lean_ctor_get(v_goal_282_, 0);
lean_inc(v_u_335_);
v_00_u03c3s_336_ = lean_ctor_get(v_goal_282_, 1);
lean_inc_ref(v_00_u03c3s_336_);
v_hyps_337_ = lean_ctor_get(v_goal_282_, 2);
lean_inc_ref(v_hyps_337_);
v_target_338_ = lean_ctor_get(v_goal_282_, 3);
lean_inc_ref(v_target_338_);
lean_dec_ref(v_goal_282_);
v___x_339_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20));
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21));
v___x_341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22));
v___x_342_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_343_ = lean_unsigned_to_nat(3u);
v___x_344_ = l_Lean_Expr_isAppOfArity(v_target_338_, v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
if (lean_obj_tag(v_target_338_) == 8)
{
lean_object* v_declName_345_; lean_object* v_type_346_; lean_object* v_value_347_; lean_object* v_body_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
lean_inc(v_toPure_334_);
lean_inc_n(v_toBind_333_, 2);
lean_dec_ref_known(v___x_331_, 3);
lean_dec_ref(v___x_324_);
v_declName_345_ = lean_ctor_get(v_target_338_, 0);
lean_inc(v_declName_345_);
v_type_346_ = lean_ctor_get(v_target_338_, 1);
lean_inc_ref(v_type_346_);
v_value_347_ = lean_ctor_get(v_target_338_, 2);
lean_inc_ref(v_value_347_);
v_body_348_ = lean_ctor_get(v_target_338_, 3);
lean_inc_ref(v_body_348_);
lean_dec_ref_known(v_target_338_, 4);
lean_inc(v_inst_281_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_349_, 0, v_inst_281_);
lean_closure_set(v___f_349_, 1, v_body_348_);
lean_closure_set(v___f_349_, 2, v_u_335_);
lean_closure_set(v___f_349_, 3, v_00_u03c3s_336_);
lean_closure_set(v___f_349_, 4, v_hyps_337_);
lean_closure_set(v___f_349_, 5, v_k_284_);
lean_closure_set(v___f_349_, 6, v_toBind_333_);
v___x_350_ = lean_box(v___x_344_);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_351_, 0, v_inst_280_);
lean_closure_set(v___f_351_, 1, v_inst_279_);
lean_closure_set(v___f_351_, 2, v_type_346_);
lean_closure_set(v___f_351_, 3, v_value_347_);
lean_closure_set(v___f_351_, 4, v___f_349_);
lean_closure_set(v___f_351_, 5, v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_283_);
v___x_353_ = l_Lean_Syntax_isOfKind(v_ident_283_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v_toPure_334_);
lean_dec(v_ident_283_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_354_, 0, v___f_351_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_355_, 0, v_declName_345_);
v___x_356_ = lean_apply_2(v_inst_281_, lean_box(0), v___f_355_);
v___x_357_ = lean_apply_4(v_toBind_333_, lean_box(0), lean_box(0), v___x_356_, v___f_354_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v_name_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v_name_359_ = l_Lean_Syntax_getArg(v_ident_283_, v___x_358_);
lean_dec(v_ident_283_);
v___x_360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_359_);
v___x_361_ = l_Lean_Syntax_isOfKind(v_name_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_name_359_);
lean_dec(v_toPure_334_);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_362_, 0, v___f_351_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed), 6, 1);
lean_closure_set(v___f_363_, 0, v_declName_345_);
v___x_364_ = lean_apply_2(v_inst_281_, lean_box(0), v___f_363_);
v___x_365_ = lean_apply_4(v_toBind_333_, lean_box(0), lean_box(0), v___x_364_, v___f_362_);
return v___x_365_;
}
else
{
lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_declName_345_);
lean_dec(v_inst_281_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3), 2, 1);
lean_closure_set(v___f_366_, 0, v___f_351_);
v___x_367_ = l_Lean_TSyntax_getId(v_name_359_);
lean_dec(v_name_359_);
v___x_368_ = lean_apply_2(v_toPure_334_, lean_box(0), v___x_367_);
v___x_369_ = lean_apply_4(v_toBind_333_, lean_box(0), lean_box(0), v___x_368_, v___f_366_);
return v___x_369_;
}
}
}
else
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_hyps_337_);
lean_dec_ref(v_00_u03c3s_336_);
lean_dec(v_u_335_);
lean_dec(v_k_284_);
lean_dec(v_ident_283_);
lean_dec_ref(v_inst_280_);
v_isSharedCheck_380_ = !lean_is_exclusive(v_inst_279_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_381_ = lean_ctor_get(v_inst_279_, 1);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_inst_279_, 0);
lean_dec(v_unused_382_);
v___x_371_ = v_inst_279_;
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
else
{
lean_dec(v_inst_279_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_374_ = l_Lean_MessageData_ofExpr(v_target_338_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 7);
lean_ctor_set(v___x_371_, 1, v___x_374_);
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_379_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l_Lean_throwError___redArg(v___x_324_, v___x_331_, v___x_376_);
v___x_378_ = lean_apply_2(v_inst_281_, lean_box(0), v___x_377_);
return v___x_378_;
}
}
}
}
else
{
lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc(v_toPure_334_);
lean_inc_n(v_toBind_333_, 2);
lean_dec_ref_known(v___x_331_, 3);
lean_dec_ref(v_inst_280_);
lean_dec_ref(v_inst_279_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed), 6, 1);
lean_closure_set(v___f_383_, 0, v_ident_283_);
v___x_384_ = l_Lean_Expr_appFn_x21(v_target_338_);
v___x_385_ = l_Lean_Expr_appFn_x21(v___x_384_);
v___x_386_ = l_Lean_Expr_appArg_x21(v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = l_Lean_Expr_appArg_x21(v___x_384_);
lean_dec_ref(v___x_384_);
v___x_388_ = l_Lean_Expr_appArg_x21(v_target_338_);
lean_dec_ref(v_target_338_);
v___x_389_ = lean_box(v___x_344_);
lean_inc(v_inst_281_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_390_, 0, v___x_387_);
lean_closure_set(v___f_390_, 1, v_u_335_);
lean_closure_set(v___f_390_, 2, v_00_u03c3s_336_);
lean_closure_set(v___f_390_, 3, v_hyps_337_);
lean_closure_set(v___f_390_, 4, v___x_339_);
lean_closure_set(v___f_390_, 5, v___x_340_);
lean_closure_set(v___f_390_, 6, v___x_341_);
lean_closure_set(v___f_390_, 7, v___x_386_);
lean_closure_set(v___f_390_, 8, v___x_388_);
lean_closure_set(v___f_390_, 9, v_toPure_334_);
lean_closure_set(v___f_390_, 10, v_k_284_);
lean_closure_set(v___f_390_, 11, v_toBind_333_);
lean_closure_set(v___f_390_, 12, v___x_389_);
lean_closure_set(v___f_390_, 13, v_inst_281_);
lean_closure_set(v___f_390_, 14, v___x_324_);
lean_closure_set(v___f_390_, 15, v___x_325_);
v___x_391_ = lean_apply_2(v_inst_281_, lean_box(0), v___f_383_);
v___x_392_ = lean_apply_4(v_toBind_333_, lean_box(0), lean_box(0), v___x_391_, v___f_390_);
return v___x_392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro(lean_object* v_m_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_goal_403_, lean_object* v_ident_404_, lean_object* v_k_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(v_inst_400_, v_inst_401_, v_inst_402_, v_goal_403_, v_ident_404_, v_k_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0(lean_object* v_u_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_hyps_416_, lean_object* v_target_417_, lean_object* v_toPure_418_, lean_object* v_prf_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_u_413_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_mkConst(v___x_420_, v___x_422_);
v___x_424_ = l_Lean_mkApp5(v___x_423_, v___x_414_, v___x_415_, v_hyps_416_, v_target_417_, v_prf_419_);
v___x_425_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_424_);
return v___x_425_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(lean_object* v___x_426_, uint8_t v___x_427_, uint8_t v___x_428_, lean_object* v_inst_429_, lean_object* v_toBind_430_, lean_object* v___f_431_, lean_object* v_prf_432_){
_start:
{
uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_433_ = 1;
v___x_434_ = lean_box(v___x_427_);
v___x_435_ = lean_box(v___x_428_);
v___x_436_ = lean_box(v___x_427_);
v___x_437_ = lean_box(v___x_428_);
v___x_438_ = lean_box(v___x_433_);
v___x_439_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_439_, 0, v___x_426_);
lean_closure_set(v___x_439_, 1, v_prf_432_);
lean_closure_set(v___x_439_, 2, v___x_434_);
lean_closure_set(v___x_439_, 3, v___x_435_);
lean_closure_set(v___x_439_, 4, v___x_436_);
lean_closure_set(v___x_439_, 5, v___x_437_);
lean_closure_set(v___x_439_, 6, v___x_438_);
v___x_440_ = lean_apply_2(v_inst_429_, lean_box(0), v___x_439_);
v___x_441_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v___x_440_, v___f_431_);
return v___x_441_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_426_ = stack[0].m_obj;
uint8_t v___x_427_ = stack[1].m_num;
uint8_t v___x_428_ = stack[2].m_num;
lean_object* v_inst_429_ = stack[3].m_obj;
lean_object* v_toBind_430_ = stack[4].m_obj;
lean_object* v___f_431_ = stack[5].m_obj;
lean_object* v_prf_432_ = stack[6].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(v___x_426_, v___x_427_, v___x_428_, v_inst_429_, v_toBind_430_, v___f_431_, v_prf_432_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed(lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v_inst_446_, lean_object* v_toBind_447_, lean_object* v___f_448_, lean_object* v_prf_449_){
_start:
{
uint8_t v___x_2139__boxed_450_; uint8_t v___x_2140__boxed_451_; lean_object* v_res_452_; 
v___x_2139__boxed_450_ = lean_unbox(v___x_444_);
v___x_2140__boxed_451_ = lean_unbox(v___x_445_);
v_res_452_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(v___x_443_, v___x_2139__boxed_450_, v___x_2140__boxed_451_, v_inst_446_, v_toBind_447_, v___f_448_, v_prf_449_);
return v_res_452_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(lean_object* v___x_453_, lean_object* v_ident_454_, uint8_t v___x_455_, lean_object* v_hyps_456_, lean_object* v___x_457_, lean_object* v_inst_458_, lean_object* v_toBind_459_, lean_object* v___f_460_, lean_object* v_target_461_, lean_object* v_u_462_, lean_object* v_k_463_, lean_object* v_map_464_, lean_object* v_s_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_lctx_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_lctx_471_ = lean_ctor_get(v___y_466_, 2);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_453_);
lean_inc_ref(v_s_465_);
lean_inc_ref(v_lctx_471_);
v___x_473_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_454_, v_lctx_471_, v_s_465_, v___x_472_, v___x_455_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec_ref_known(v___x_473_, 1);
lean_inc_ref(v_s_465_);
v___x_474_ = l_Lean_Expr_app___override(v_hyps_456_, v_s_465_);
lean_inc_ref(v___x_457_);
v___x_475_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_457_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_mk_empty_array_with_capacity(v___x_476_);
v___x_478_ = lean_array_push(v___x_477_, v_s_465_);
v___x_479_ = 0;
v___x_480_ = lean_box(v___x_479_);
v___x_481_ = lean_box(v___x_455_);
lean_inc(v_toBind_459_);
lean_inc_ref(v___x_478_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_482_, 0, v___x_478_);
lean_closure_set(v___f_482_, 1, v___x_480_);
lean_closure_set(v___f_482_, 2, v___x_481_);
lean_closure_set(v___f_482_, 3, v_inst_458_);
lean_closure_set(v___f_482_, 4, v_toBind_459_);
lean_closure_set(v___f_482_, 5, v___f_460_);
v___x_483_ = l_Lean_Expr_betaRev(v_target_461_, v___x_478_, v___x_479_, v___x_479_);
lean_dec_ref(v___x_478_);
v___x_484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_484_, 0, v_u_462_);
lean_ctor_set(v___x_484_, 1, v___x_457_);
lean_ctor_set(v___x_484_, 2, v___x_475_);
lean_ctor_set(v___x_484_, 3, v___x_483_);
v___x_485_ = lean_apply_1(v_k_463_, v___x_484_);
v___x_486_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_485_, v___f_482_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
v___x_487_ = lean_apply_7(v_map_464_, lean_box(0), v___x_486_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, lean_box(0));
return v___x_487_;
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_s_465_);
lean_dec_ref(v_map_464_);
lean_dec(v_k_463_);
lean_dec(v_u_462_);
lean_dec_ref(v_target_461_);
lean_dec(v___f_460_);
lean_dec(v_toBind_459_);
lean_dec(v_inst_458_);
lean_dec_ref(v___x_457_);
lean_dec_ref(v_hyps_456_);
v_a_488_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_473_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_473_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_453_ = stack[0].m_obj;
lean_object* v_ident_454_ = stack[1].m_obj;
uint8_t v___x_455_ = stack[2].m_num;
lean_object* v_hyps_456_ = stack[3].m_obj;
lean_object* v___x_457_ = stack[4].m_obj;
lean_object* v_inst_458_ = stack[5].m_obj;
lean_object* v_toBind_459_ = stack[6].m_obj;
lean_object* v___f_460_ = stack[7].m_obj;
lean_object* v_target_461_ = stack[8].m_obj;
lean_object* v_u_462_ = stack[9].m_obj;
lean_object* v_k_463_ = stack[10].m_obj;
lean_object* v_map_464_ = stack[11].m_obj;
lean_object* v_s_465_ = stack[12].m_obj;
lean_object* v___y_466_ = stack[13].m_obj;
lean_object* v___y_467_ = stack[14].m_obj;
lean_object* v___y_468_ = stack[15].m_obj;
lean_object* v___y_469_ = stack[16].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(v___x_453_, v_ident_454_, v___x_455_, v_hyps_456_, v___x_457_, v_inst_458_, v_toBind_459_, v___f_460_, v_target_461_, v_u_462_, v_k_463_, v_map_464_, v_s_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_497_ = _args[0];
lean_object* v_ident_498_ = _args[1];
lean_object* v___x_499_ = _args[2];
lean_object* v_hyps_500_ = _args[3];
lean_object* v___x_501_ = _args[4];
lean_object* v_inst_502_ = _args[5];
lean_object* v_toBind_503_ = _args[6];
lean_object* v___f_504_ = _args[7];
lean_object* v_target_505_ = _args[8];
lean_object* v_u_506_ = _args[9];
lean_object* v_k_507_ = _args[10];
lean_object* v_map_508_ = _args[11];
lean_object* v_s_509_ = _args[12];
lean_object* v___y_510_ = _args[13];
lean_object* v___y_511_ = _args[14];
lean_object* v___y_512_ = _args[15];
lean_object* v___y_513_ = _args[16];
lean_object* v___y_514_ = _args[17];
_start:
{
uint8_t v___x_2191__boxed_515_; lean_object* v_res_516_; 
v___x_2191__boxed_515_ = lean_unbox(v___x_499_);
v_res_516_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(v___x_497_, v_ident_498_, v___x_2191__boxed_515_, v_hyps_500_, v___x_501_, v_inst_502_, v_toBind_503_, v___f_504_, v_target_505_, v_u_506_, v_k_507_, v_map_508_, v_s_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_516_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(lean_object* v_goal_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v_toPure_531_, lean_object* v_ident_532_, lean_object* v_inst_533_, lean_object* v_toBind_534_, lean_object* v_k_535_, lean_object* v___x_536_, lean_object* v_map_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_u_543_; lean_object* v_00_u03c3s_544_; lean_object* v_hyps_545_; lean_object* v_target_546_; lean_object* v___x_547_; 
v_u_543_ = lean_ctor_get(v_goal_528_, 0);
lean_inc(v_u_543_);
v_00_u03c3s_544_ = lean_ctor_get(v_goal_528_, 1);
lean_inc_ref_n(v_00_u03c3s_544_, 2);
v_hyps_545_ = lean_ctor_get(v_goal_528_, 2);
lean_inc_ref(v_hyps_545_);
v_target_546_ = lean_ctor_get(v_goal_528_, 3);
lean_inc_ref(v_target_546_);
lean_dec_ref(v_goal_528_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
v___x_547_ = lean_whnf(v_00_u03c3s_544_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_550_ = lean_unsigned_to_nat(3u);
v___x_551_ = l_Lean_Expr_isAppOfArity(v_a_548_, v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_2049__overap_555_; lean_object* v___x_556_; 
lean_dec(v_a_548_);
lean_dec_ref(v_target_546_);
lean_dec_ref(v_hyps_545_);
lean_dec(v_u_543_);
lean_dec_ref(v_map_537_);
lean_dec_ref(v___x_536_);
lean_dec(v_k_535_);
lean_dec(v_toBind_534_);
lean_dec(v_inst_533_);
lean_dec(v_ident_532_);
lean_dec(v_toPure_531_);
v___x_552_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_553_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_544_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_2049__overap_555_ = l_Lean_throwError___redArg(v___x_529_, v___x_530_, v___x_554_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
v___x_556_ = lean_apply_5(v___x_2049__overap_555_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___f_560_; lean_object* v___x_561_; lean_object* v___f_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
lean_dec_ref(v_00_u03c3s_544_);
lean_dec_ref(v___x_530_);
v___x_557_ = l_Lean_Expr_appFn_x21(v_a_548_);
v___x_558_ = l_Lean_Expr_appArg_x21(v___x_557_);
lean_dec_ref(v___x_557_);
v___x_559_ = l_Lean_Expr_appArg_x21(v_a_548_);
lean_dec(v_a_548_);
lean_inc_ref(v_target_546_);
lean_inc_ref(v_hyps_545_);
lean_inc_ref_n(v___x_558_, 2);
lean_inc_ref(v___x_559_);
lean_inc(v_u_543_);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0), 7, 6);
lean_closure_set(v___f_560_, 0, v_u_543_);
lean_closure_set(v___f_560_, 1, v___x_559_);
lean_closure_set(v___f_560_, 2, v___x_558_);
lean_closure_set(v___f_560_, 3, v_hyps_545_);
lean_closure_set(v___f_560_, 4, v_target_546_);
lean_closure_set(v___f_560_, 5, v_toPure_531_);
v___x_561_ = lean_box(v___x_551_);
lean_inc_n(v_ident_532_, 2);
v___f_562_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed), 18, 12);
lean_closure_set(v___f_562_, 0, v___x_558_);
lean_closure_set(v___f_562_, 1, v_ident_532_);
lean_closure_set(v___f_562_, 2, v___x_561_);
lean_closure_set(v___f_562_, 3, v_hyps_545_);
lean_closure_set(v___f_562_, 4, v___x_559_);
lean_closure_set(v___f_562_, 5, v_inst_533_);
lean_closure_set(v___f_562_, 6, v_toBind_534_);
lean_closure_set(v___f_562_, 7, v___f_560_);
lean_closure_set(v___f_562_, 8, v_target_546_);
lean_closure_set(v___f_562_, 9, v_u_543_);
lean_closure_set(v___f_562_, 10, v_k_535_);
lean_closure_set(v___f_562_, 11, v_map_537_);
v___x_563_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_564_ = l_Lean_Syntax_isOfKind(v_ident_532_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_ident_532_);
v___x_565_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_566_ = l_Lean_Core_mkFreshUserName(v___x_565_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_2064__overap_568_; lean_object* v___x_569_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_2064__overap_568_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_536_, v___x_529_, v_a_567_, v___x_558_, v___f_562_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
v___x_569_ = lean_apply_5(v___x_2064__overap_568_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
return v___x_569_;
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v___f_562_);
lean_dec_ref(v___x_558_);
lean_dec_ref(v___x_536_);
lean_dec_ref(v___x_529_);
v_a_570_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_566_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_566_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = l_Lean_Syntax_getArg(v_ident_532_, v___x_578_);
lean_dec(v_ident_532_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_579_);
v___x_581_ = l_Lean_Syntax_isOfKind(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_579_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_583_ = l_Lean_Core_mkFreshUserName(v___x_582_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_2078__overap_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_2078__overap_585_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_536_, v___x_529_, v_a_584_, v___x_558_, v___f_562_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
v___x_586_ = lean_apply_5(v___x_2078__overap_585_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
return v___x_586_;
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v___f_562_);
lean_dec_ref(v___x_558_);
lean_dec_ref(v___x_536_);
lean_dec_ref(v___x_529_);
v_a_587_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_583_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_583_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_2083__overap_596_; lean_object* v___x_597_; 
v___x_595_ = l_Lean_TSyntax_getId(v___x_579_);
lean_dec(v___x_579_);
v___x_2083__overap_596_ = l_Lean_Meta_withLocalDeclD___redArg(v___x_536_, v___x_529_, v___x_595_, v___x_558_, v___f_562_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
v___x_597_ = lean_apply_5(v___x_2083__overap_596_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_target_546_);
lean_dec_ref(v_hyps_545_);
lean_dec_ref(v_00_u03c3s_544_);
lean_dec(v_u_543_);
lean_dec_ref(v_map_537_);
lean_dec_ref(v___x_536_);
lean_dec(v_k_535_);
lean_dec(v_toBind_534_);
lean_dec(v_inst_533_);
lean_dec(v_ident_532_);
lean_dec(v_toPure_531_);
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_529_);
v_a_598_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_547_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_547_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_528_ = stack[0].m_obj;
lean_object* v___x_529_ = stack[1].m_obj;
lean_object* v___x_530_ = stack[2].m_obj;
lean_object* v_toPure_531_ = stack[3].m_obj;
lean_object* v_ident_532_ = stack[4].m_obj;
lean_object* v_inst_533_ = stack[5].m_obj;
lean_object* v_toBind_534_ = stack[6].m_obj;
lean_object* v_k_535_ = stack[7].m_obj;
lean_object* v___x_536_ = stack[8].m_obj;
lean_object* v_map_537_ = stack[9].m_obj;
lean_object* v___y_538_ = stack[10].m_obj;
lean_object* v___y_539_ = stack[11].m_obj;
lean_object* v___y_540_ = stack[12].m_obj;
lean_object* v___y_541_ = stack[13].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(v_goal_528_, v___x_529_, v___x_530_, v_toPure_531_, v_ident_532_, v_inst_533_, v_toBind_534_, v_k_535_, v___x_536_, v_map_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed(lean_object* v_goal_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v_toPure_610_, lean_object* v_ident_611_, lean_object* v_inst_612_, lean_object* v_toBind_613_, lean_object* v_k_614_, lean_object* v___x_615_, lean_object* v_map_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(v_goal_607_, v___x_608_, v___x_609_, v_toPure_610_, v_ident_611_, v_inst_612_, v_toBind_613_, v_k_614_, v___x_615_, v_map_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_goal_626_, lean_object* v_ident_627_, lean_object* v_k_628_){
_start:
{
lean_object* v___x_629_; lean_object* v_toApplicative_630_; lean_object* v_toFunctor_631_; lean_object* v_toSeq_632_; lean_object* v_toSeqLeft_633_; lean_object* v_toSeqRight_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_toApplicative_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_704_; 
v___x_629_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1);
v_toApplicative_630_ = lean_ctor_get(v___x_629_, 0);
v_toFunctor_631_ = lean_ctor_get(v_toApplicative_630_, 0);
v_toSeq_632_ = lean_ctor_get(v_toApplicative_630_, 2);
v_toSeqLeft_633_ = lean_ctor_get(v_toApplicative_630_, 3);
v_toSeqRight_634_ = lean_ctor_get(v_toApplicative_630_, 4);
v___f_635_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2));
v___f_636_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_631_, 2);
v___f_637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_637_, 0, v_toFunctor_631_);
v___f_638_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_638_, 0, v_toFunctor_631_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___f_637_);
lean_ctor_set(v___x_639_, 1, v___f_638_);
lean_inc(v_toSeqRight_634_);
v___f_640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_640_, 0, v_toSeqRight_634_);
lean_inc(v_toSeqLeft_633_);
v___f_641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_641_, 0, v_toSeqLeft_633_);
lean_inc(v_toSeq_632_);
v___f_642_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_642_, 0, v_toSeq_632_);
v___x_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_643_, 0, v___x_639_);
lean_ctor_set(v___x_643_, 1, v___f_635_);
lean_ctor_set(v___x_643_, 2, v___f_642_);
lean_ctor_set(v___x_643_, 3, v___f_641_);
lean_ctor_set(v___x_643_, 4, v___f_640_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___f_636_);
v___x_645_ = l_StateRefT_x27_instMonad___redArg(v___x_644_);
v_toApplicative_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_645_, 1);
lean_dec(v_unused_705_);
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_704_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_toApplicative_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_704_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_toFunctor_650_; lean_object* v_toSeq_651_; lean_object* v_toSeqLeft_652_; lean_object* v_toSeqRight_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_702_; 
v_toFunctor_650_ = lean_ctor_get(v_toApplicative_646_, 0);
v_toSeq_651_ = lean_ctor_get(v_toApplicative_646_, 2);
v_toSeqLeft_652_ = lean_ctor_get(v_toApplicative_646_, 3);
v_toSeqRight_653_ = lean_ctor_get(v_toApplicative_646_, 4);
v_isSharedCheck_702_ = !lean_is_exclusive(v_toApplicative_646_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_dec(v_unused_703_);
v___x_655_ = v_toApplicative_646_;
v_isShared_656_ = v_isSharedCheck_702_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_toSeqRight_653_);
lean_inc(v_toSeqLeft_652_);
lean_inc(v_toSeq_651_);
lean_inc(v_toFunctor_650_);
lean_dec(v_toApplicative_646_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_702_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_666_; 
v___f_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6));
v___f_658_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7));
lean_inc_ref(v_toFunctor_650_);
v___f_659_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_659_, 0, v_toFunctor_650_);
v___f_660_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_660_, 0, v_toFunctor_650_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___f_659_);
lean_ctor_set(v___x_661_, 1, v___f_660_);
v___f_662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_662_, 0, v_toSeqRight_653_);
v___f_663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_663_, 0, v_toSeqLeft_652_);
v___f_664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_664_, 0, v_toSeq_651_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v___f_662_);
lean_ctor_set(v___x_655_, 3, v___f_663_);
lean_ctor_set(v___x_655_, 2, v___f_664_);
lean_ctor_set(v___x_655_, 1, v___f_657_);
lean_ctor_set(v___x_655_, 0, v___x_661_);
v___x_666_ = v___x_655_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___f_657_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___f_664_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v___f_663_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v___f_662_);
v___x_666_ = v_reuseFailAlloc_701_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___f_658_);
lean_ctor_set(v___x_648_, 0, v___x_666_);
v___x_668_ = v___x_648_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___f_658_);
v___x_668_ = v_reuseFailAlloc_700_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v_toApplicative_669_; lean_object* v_toFunctor_670_; lean_object* v_toSeq_671_; lean_object* v_toSeqLeft_672_; lean_object* v_toSeqRight_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___f_677_; lean_object* v___f_678_; lean_object* v___f_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_toMonadRef_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_toApplicative_691_; lean_object* v_toBind_692_; lean_object* v_toPure_693_; lean_object* v_liftWith_694_; lean_object* v_restoreM_695_; lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_toApplicative_669_ = lean_ctor_get(v___x_629_, 0);
v_toFunctor_670_ = lean_ctor_get(v_toApplicative_669_, 0);
v_toSeq_671_ = lean_ctor_get(v_toApplicative_669_, 2);
v_toSeqLeft_672_ = lean_ctor_get(v_toApplicative_669_, 3);
v_toSeqRight_673_ = lean_ctor_get(v_toApplicative_669_, 4);
lean_inc_ref_n(v_toFunctor_670_, 2);
v___f_674_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_674_, 0, v_toFunctor_670_);
v___f_675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_675_, 0, v_toFunctor_670_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___f_674_);
lean_ctor_set(v___x_676_, 1, v___f_675_);
lean_inc(v_toSeqRight_673_);
v___f_677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_677_, 0, v_toSeqRight_673_);
lean_inc(v_toSeqLeft_672_);
v___f_678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_678_, 0, v_toSeqLeft_672_);
lean_inc(v_toSeq_671_);
v___f_679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_679_, 0, v_toSeq_671_);
v___x_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_680_, 0, v___x_676_);
lean_ctor_set(v___x_680_, 1, v___f_635_);
lean_ctor_set(v___x_680_, 2, v___f_679_);
lean_ctor_set(v___x_680_, 3, v___f_678_);
lean_ctor_set(v___x_680_, 4, v___f_677_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___f_636_);
v___x_682_ = l_StateRefT_x27_instMonad___redArg(v___x_681_);
v___x_683_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_683_, 0, lean_box(0));
lean_closure_set(v___x_683_, 1, lean_box(0));
lean_closure_set(v___x_683_, 2, v___x_682_);
v___x_684_ = l_instMonadControlTOfPure___redArg(v___x_683_);
v___x_685_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15);
v___x_686_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19);
v_toMonadRef_687_ = lean_ctor_get(v___x_686_, 0);
v___x_688_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_668_);
v___x_689_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_688_, v___x_668_);
lean_inc_ref(v_toMonadRef_687_);
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v___x_685_);
lean_ctor_set(v___x_690_, 1, v_toMonadRef_687_);
lean_ctor_set(v___x_690_, 2, v___x_689_);
v_toApplicative_691_ = lean_ctor_get(v_inst_623_, 0);
lean_inc_ref(v_toApplicative_691_);
v_toBind_692_ = lean_ctor_get(v_inst_623_, 1);
lean_inc_n(v_toBind_692_, 2);
lean_dec_ref(v_inst_623_);
v_toPure_693_ = lean_ctor_get(v_toApplicative_691_, 1);
lean_inc(v_toPure_693_);
lean_dec_ref(v_toApplicative_691_);
v_liftWith_694_ = lean_ctor_get(v_inst_624_, 0);
lean_inc(v_liftWith_694_);
v_restoreM_695_ = lean_ctor_get(v_inst_624_, 1);
lean_inc(v_restoreM_695_);
lean_dec_ref(v_inst_624_);
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed), 15, 9);
lean_closure_set(v___f_696_, 0, v_goal_626_);
lean_closure_set(v___f_696_, 1, v___x_668_);
lean_closure_set(v___f_696_, 2, v___x_690_);
lean_closure_set(v___f_696_, 3, v_toPure_693_);
lean_closure_set(v___f_696_, 4, v_ident_627_);
lean_closure_set(v___f_696_, 5, v_inst_625_);
lean_closure_set(v___f_696_, 6, v_toBind_692_);
lean_closure_set(v___f_696_, 7, v_k_628_);
lean_closure_set(v___f_696_, 8, v___x_684_);
v___x_697_ = lean_apply_2(v_liftWith_694_, lean_box(0), v___f_696_);
v___x_698_ = lean_apply_1(v_restoreM_695_, lean_box(0));
v___x_699_ = lean_apply_4(v_toBind_692_, lean_box(0), lean_box(0), v___x_697_, v___x_698_);
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall(lean_object* v_m_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_goal_710_, lean_object* v_ident_711_, lean_object* v_k_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_707_, v_inst_708_, v_inst_709_, v_goal_710_, v_ident_711_, v_k_712_);
return v___x_713_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(uint8_t v_isZero_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_ref_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_ref_729_ = lean_ctor_get(v___y_726_, 2);
v___x_730_ = l_Lean_SourceInfo_fromRef(v_ref_729_, v_isZero_723_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3));
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4));
lean_inc_n(v___x_730_, 2);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_730_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Syntax_node1(v___x_730_, v___x_732_, v___x_734_);
v___x_736_ = l_Lean_Syntax_node1(v___x_730_, v___x_731_, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_isZero_723_ = stack[0].m_num;
lean_object* v___y_724_ = stack[1].m_obj;
lean_object* v___y_725_ = stack[2].m_obj;
lean_object* v___y_726_ = stack[3].m_obj;
lean_object* v___y_727_ = stack[4].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(v_isZero_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed(lean_object* v_isZero_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
uint8_t v_isZero_boxed_745_; lean_object* v_res_746_; 
v_isZero_boxed_745_ = lean_unbox(v_isZero_739_);
v_res_746_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(v_isZero_boxed_745_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2(lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_goal_750_, lean_object* v___f_751_, lean_object* v_____do__lift_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(v_inst_747_, v_inst_748_, v_inst_749_, v_goal_750_, v_____do__lift_752_, v___f_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed(lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_n_757_, lean_object* v_k_758_, lean_object* v_g_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(v_inst_754_, v_inst_755_, v_inst_756_, v_n_757_, v_k_758_, v_g_759_);
lean_dec(v_n_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_goal_764_, lean_object* v_n_765_, lean_object* v_k_766_){
_start:
{
lean_object* v_toBind_767_; lean_object* v_zero_768_; uint8_t v_isZero_769_; 
v_toBind_767_ = lean_ctor_get(v_inst_761_, 1);
lean_inc(v_toBind_767_);
v_zero_768_ = lean_unsigned_to_nat(0u);
v_isZero_769_ = lean_nat_dec_eq(v_n_765_, v_zero_768_);
if (v_isZero_769_ == 1)
{
lean_object* v___x_770_; 
lean_dec(v_toBind_767_);
lean_dec(v_inst_763_);
lean_dec_ref(v_inst_762_);
lean_dec_ref(v_inst_761_);
v___x_770_ = lean_apply_1(v_k_766_, v_goal_764_);
return v___x_770_;
}
else
{
lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v_one_773_; lean_object* v_n_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_771_ = lean_box(v_isZero_769_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_772_, 0, v___x_771_);
v_one_773_ = lean_unsigned_to_nat(1u);
v_n_774_ = lean_nat_sub(v_n_765_, v_one_773_);
lean_inc_n(v_inst_763_, 2);
lean_inc_ref(v_inst_762_);
lean_inc_ref(v_inst_761_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_775_, 0, v_inst_761_);
lean_closure_set(v___f_775_, 1, v_inst_762_);
lean_closure_set(v___f_775_, 2, v_inst_763_);
lean_closure_set(v___f_775_, 3, v_n_774_);
lean_closure_set(v___f_775_, 4, v_k_766_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2), 6, 5);
lean_closure_set(v___f_776_, 0, v_inst_761_);
lean_closure_set(v___f_776_, 1, v_inst_762_);
lean_closure_set(v___f_776_, 2, v_inst_763_);
lean_closure_set(v___f_776_, 3, v_goal_764_);
lean_closure_set(v___f_776_, 4, v___f_775_);
v___x_777_ = lean_apply_2(v_inst_763_, lean_box(0), v___f_772_);
v___x_778_ = lean_apply_4(v_toBind_767_, lean_box(0), lean_box(0), v___x_777_, v___f_776_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_n_782_, lean_object* v_k_783_, lean_object* v_g_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_779_, v_inst_780_, v_inst_781_, v_g_784_, v_n_782_, v_k_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___boxed(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_goal_789_, lean_object* v_n_790_, lean_object* v_k_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_786_, v_inst_787_, v_inst_788_, v_goal_789_, v_n_790_, v_k_791_);
lean_dec(v_n_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(lean_object* v_m_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_goal_797_, lean_object* v_n_798_, lean_object* v_k_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(v_inst_794_, v_inst_795_, v_inst_796_, v_goal_797_, v_n_798_, v_k_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___boxed(lean_object* v_m_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_goal_805_, lean_object* v_n_806_, lean_object* v_k_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(v_m_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_goal_805_, v_n_806_, v_k_807_);
lean_dec(v_n_806_);
return v_res_808_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10));
v___x_838_ = l_String_toRawSubstring_x27(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_852_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0));
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc(v_x_849_);
v___x_854_ = l_Lean_Syntax_isOfKind(v_x_849_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v_x_849_);
v___x_855_ = lean_box(1);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_a_851_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = l_Lean_Syntax_getArg(v_x_849_, v___x_858_);
lean_dec(v_x_849_);
v___x_860_ = lean_unsigned_to_nat(2u);
v___x_861_ = l_Lean_Syntax_getNumArgs(v___x_859_);
v___x_862_ = lean_nat_dec_le(v___x_860_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
lean_dec(v___x_861_);
lean_inc(v___x_859_);
v___x_863_ = l_Lean_Syntax_matchesNull(v___x_859_, v___x_858_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v___x_859_);
v___x_864_ = lean_box(1);
v___x_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_a_851_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_866_ = l_Lean_Syntax_getArg(v___x_859_, v___x_857_);
lean_dec(v___x_859_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3));
lean_inc(v___x_866_);
v___x_868_ = l_Lean_Syntax_isOfKind(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v___x_866_);
v___x_869_ = l_Lean_Macro_throwUnsupported___redArg(v_a_851_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_870_ = l_Lean_Syntax_getArg(v___x_866_, v___x_857_);
lean_dec(v___x_866_);
v___x_871_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_870_);
v___x_872_ = l_Lean_Syntax_isOfKind(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v_quotContext_873_; lean_object* v_currMacroScope_874_; lean_object* v_ref_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_quotContext_873_ = lean_ctor_get(v_a_850_, 1);
v_currMacroScope_874_ = lean_ctor_get(v_a_850_, 2);
v_ref_875_ = lean_ctor_get(v_a_850_, 5);
v___x_876_ = l_Lean_SourceInfo_fromRef(v_ref_875_, v___x_872_);
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc_n(v___x_876_, 12);
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_876_);
lean_ctor_set(v___x_879_, 1, v___x_852_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
lean_inc(v_currMacroScope_874_);
lean_inc(v_quotContext_873_);
v___x_883_ = l_Lean_addMacroScope(v_quotContext_873_, v___x_882_, v_currMacroScope_874_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_885_, 0, v___x_876_);
lean_ctor_set(v___x_885_, 1, v___x_881_);
lean_ctor_set(v___x_885_, 2, v___x_883_);
lean_ctor_set(v___x_885_, 3, v___x_884_);
lean_inc_ref(v___x_885_);
v___x_886_ = l_Lean_Syntax_node1(v___x_876_, v___x_880_, v___x_885_);
v___x_887_ = l_Lean_Syntax_node1(v___x_876_, v___x_871_, v___x_886_);
v___x_888_ = l_Lean_Syntax_node1(v___x_876_, v___x_867_, v___x_887_);
v___x_889_ = l_Lean_Syntax_node1(v___x_876_, v___x_878_, v___x_888_);
v___x_890_ = l_Lean_Syntax_node2(v___x_876_, v___x_853_, v___x_879_, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
v___x_892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_876_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
v___x_895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_876_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
v___x_896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
v___x_897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_876_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_Syntax_node4(v___x_876_, v___x_894_, v___x_895_, v___x_885_, v___x_897_, v___x_870_);
v___x_899_ = l_Lean_Syntax_node3(v___x_876_, v___x_878_, v___x_890_, v___x_892_, v___x_898_);
v___x_900_ = l_Lean_Syntax_node1(v___x_876_, v___x_877_, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_a_851_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = l_Lean_Syntax_getArg(v___x_870_, v___x_857_);
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_904_ = l_Lean_Syntax_isOfKind(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v_quotContext_905_; lean_object* v_currMacroScope_906_; lean_object* v_ref_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_quotContext_905_ = lean_ctor_get(v_a_850_, 1);
v_currMacroScope_906_ = lean_ctor_get(v_a_850_, 2);
v_ref_907_ = lean_ctor_get(v_a_850_, 5);
v___x_908_ = l_Lean_SourceInfo_fromRef(v_ref_907_, v___x_904_);
v___x_909_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
lean_inc_n(v___x_908_, 12);
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_908_);
lean_ctor_set(v___x_911_, 1, v___x_852_);
v___x_912_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12));
lean_inc(v_currMacroScope_906_);
lean_inc(v_quotContext_905_);
v___x_914_ = l_Lean_addMacroScope(v_quotContext_905_, v___x_913_, v_currMacroScope_906_);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_916_, 0, v___x_908_);
lean_ctor_set(v___x_916_, 1, v___x_912_);
lean_ctor_set(v___x_916_, 2, v___x_914_);
lean_ctor_set(v___x_916_, 3, v___x_915_);
lean_inc_ref(v___x_916_);
v___x_917_ = l_Lean_Syntax_node1(v___x_908_, v___x_903_, v___x_916_);
v___x_918_ = l_Lean_Syntax_node1(v___x_908_, v___x_871_, v___x_917_);
v___x_919_ = l_Lean_Syntax_node1(v___x_908_, v___x_867_, v___x_918_);
v___x_920_ = l_Lean_Syntax_node1(v___x_908_, v___x_910_, v___x_919_);
v___x_921_ = l_Lean_Syntax_node2(v___x_908_, v___x_853_, v___x_911_, v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_908_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14));
v___x_925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15));
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_908_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
v___x_927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16));
v___x_928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_908_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_Syntax_node4(v___x_908_, v___x_925_, v___x_926_, v___x_916_, v___x_928_, v___x_870_);
v___x_930_ = l_Lean_Syntax_node3(v___x_908_, v___x_910_, v___x_921_, v___x_923_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node1(v___x_908_, v___x_909_, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v_a_851_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; 
lean_dec(v___x_870_);
v___x_933_ = l_Lean_Macro_throwUnsupported___redArg(v_a_851_);
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v_ref_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_pats_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_ref_934_ = lean_ctor_get(v_a_850_, 5);
v___x_935_ = l_Lean_Syntax_getArg(v___x_859_, v___x_857_);
v___x_936_ = l_Lean_Syntax_getArg(v___x_859_, v___x_858_);
v___x_937_ = l_Lean_Syntax_getArgs(v___x_859_);
lean_dec(v___x_859_);
v___x_938_ = l_Array_extract___redArg(v___x_937_, v___x_860_, v___x_861_);
lean_dec_ref(v___x_937_);
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9));
v___x_940_ = lean_box(2);
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_938_);
v_pats_942_ = l_Lean_Syntax_getArgs(v___x_941_);
lean_dec_ref_known(v___x_941_, 3);
v___x_943_ = 0;
v___x_944_ = l_Lean_SourceInfo_fromRef(v_ref_934_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7));
lean_inc_n(v___x_944_, 7);
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_852_);
v___x_947_ = l_Lean_Syntax_node1(v___x_944_, v___x_939_, v___x_935_);
lean_inc_ref(v___x_946_);
v___x_948_ = l_Lean_Syntax_node2(v___x_944_, v___x_853_, v___x_946_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13));
v___x_950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_944_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Array_mkArray1___redArg(v___x_936_);
v___x_952_ = l_Array_append___redArg(v___x_951_, v_pats_942_);
lean_dec_ref(v_pats_942_);
v___x_953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_953_, 0, v___x_944_);
lean_ctor_set(v___x_953_, 1, v___x_939_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
v___x_954_ = l_Lean_Syntax_node2(v___x_944_, v___x_853_, v___x_946_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node3(v___x_944_, v___x_939_, v___x_948_, v___x_950_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node1(v___x_944_, v___x_945_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_851_);
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object* v_x_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(v_x_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_961_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_box(0);
v___x_963_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
return v___x_964_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_968_;
v_res_968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___boxed(lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v_res_970_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(lean_object* v_00_u03b1_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_981_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_972_ = stack[1].m_obj;
lean_object* v___y_973_ = stack[2].m_obj;
lean_object* v___y_974_ = stack[3].m_obj;
lean_object* v___y_975_ = stack[4].m_obj;
lean_object* v___y_976_ = stack[5].m_obj;
lean_object* v___y_977_ = stack[6].m_obj;
lean_object* v___y_978_ = stack[7].m_obj;
lean_object* v___y_979_ = stack[8].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(lean_box(0), v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___boxed(lean_object* v_00_u03b1_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(v_00_u03b1_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_993_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
v___x_1004_ = lean_apply_9(v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_994_ = stack[0].m_obj;
lean_object* v___y_995_ = stack[1].m_obj;
lean_object* v___y_996_ = stack[2].m_obj;
lean_object* v___y_997_ = stack[3].m_obj;
lean_object* v___y_998_ = stack[4].m_obj;
lean_object* v___y_999_ = stack[5].m_obj;
lean_object* v___y_1000_ = stack[6].m_obj;
lean_object* v___y_1001_ = stack[7].m_obj;
lean_object* v___y_1002_ = stack[8].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed(lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1016_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(lean_object* v_mvarId_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___f_1028_; lean_object* v___x_1029_; 
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1028_, 0, v_x_1018_);
lean_closure_set(v___f_1028_, 1, v___y_1019_);
lean_closure_set(v___f_1028_, 2, v___y_1020_);
lean_closure_set(v___f_1028_, 3, v___y_1021_);
lean_closure_set(v___f_1028_, 4, v___y_1022_);
v___x_1029_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1017_, v___f_1028_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1029_) == 0)
{
return v___x_1029_;
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1017_ = stack[0].m_obj;
lean_object* v_x_1018_ = stack[1].m_obj;
lean_object* v___y_1019_ = stack[2].m_obj;
lean_object* v___y_1020_ = stack[3].m_obj;
lean_object* v___y_1021_ = stack[4].m_obj;
lean_object* v___y_1022_ = stack[5].m_obj;
lean_object* v___y_1023_ = stack[6].m_obj;
lean_object* v___y_1024_ = stack[7].m_obj;
lean_object* v___y_1025_ = stack[8].m_obj;
lean_object* v___y_1026_ = stack[9].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___boxed(lean_object* v_mvarId_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1039_, v_x_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1050_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(lean_object* v_00_u03b1_1051_, lean_object* v_mvarId_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_1052_, v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1052_ = stack[1].m_obj;
lean_object* v_x_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v___y_1057_ = stack[6].m_obj;
lean_object* v___y_1058_ = stack[7].m_obj;
lean_object* v___y_1059_ = stack[8].m_obj;
lean_object* v___y_1060_ = stack[9].m_obj;
lean_object* v___y_1061_ = stack[10].m_obj;
lean_object* v_res_1064_;
v_res_1064_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(lean_box(0), v_mvarId_1052_, v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
stack->m_obj
 = v_res_1064_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_mvarId_1066_, lean_object* v_x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(v_00_u03b1_1065_, v_mvarId_1066_, v_x_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1077_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(lean_object* v_val_1078_, lean_object* v_newGoal_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1079_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1089_, v___x_1090_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1103_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1096_ = lean_st_ref_take(v_val_1078_);
v___x_1097_ = l_Lean_Expr_mvarId_x21(v_a_1092_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1096_);
v___x_1099_ = lean_st_ref_put(v_val_1078_, v___x_1098_);
if (v_isShared_1095_ == 0)
{
v___x_1101_ = v___x_1094_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1092_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
return v___x_1091_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1078_ = stack[0].m_obj;
lean_object* v_newGoal_1079_ = stack[1].m_obj;
lean_object* v___y_1080_ = stack[2].m_obj;
lean_object* v___y_1081_ = stack[3].m_obj;
lean_object* v___y_1082_ = stack[4].m_obj;
lean_object* v___y_1083_ = stack[5].m_obj;
lean_object* v___y_1084_ = stack[6].m_obj;
lean_object* v___y_1085_ = stack[7].m_obj;
lean_object* v___y_1086_ = stack[8].m_obj;
lean_object* v___y_1087_ = stack[9].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(v_val_1078_, v_newGoal_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed(lean_object* v_val_1105_, lean_object* v_newGoal_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(v_val_1105_, v_newGoal_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v_val_1105_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v_ks_1121_; lean_object* v_vs_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1146_; 
v_ks_1121_ = lean_ctor_get(v_x_1117_, 0);
v_vs_1122_ = lean_ctor_get(v_x_1117_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_x_1117_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1124_ = v_x_1117_;
v_isShared_1125_ = v_isSharedCheck_1146_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_vs_1122_);
lean_inc(v_ks_1121_);
lean_dec(v_x_1117_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1146_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_array_get_size(v_ks_1121_);
v___x_1127_ = lean_nat_dec_lt(v_x_1118_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
lean_dec(v_x_1118_);
v___x_1128_ = lean_array_push(v_ks_1121_, v_x_1119_);
v___x_1129_ = lean_array_push(v_vs_1122_, v_x_1120_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___x_1129_);
lean_ctor_set(v___x_1124_, 0, v___x_1128_);
v___x_1131_ = v___x_1124_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
lean_object* v_k_x27_1133_; uint8_t v___x_1134_; 
v_k_x27_1133_ = lean_array_fget_borrowed(v_ks_1121_, v_x_1118_);
v___x_1134_ = l_Lean_instBEqMVarId_beq(v_x_1119_, v_k_x27_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1136_; 
if (v_isShared_1125_ == 0)
{
v___x_1136_ = v___x_1124_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_ks_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_vs_1122_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_x_1118_, v___x_1137_);
lean_dec(v_x_1118_);
v_x_1117_ = v___x_1136_;
v_x_1118_ = v___x_1138_;
goto _start;
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1141_ = lean_array_fset(v_ks_1121_, v_x_1118_, v_x_1119_);
v___x_1142_ = lean_array_fset(v_vs_1122_, v_x_1118_, v_x_1120_);
lean_dec(v_x_1118_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___x_1142_);
lean_ctor_set(v___x_1124_, 0, v___x_1141_);
v___x_1144_ = v___x_1124_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_n_1147_, lean_object* v_k_1148_, lean_object* v_v_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_n_1147_, v___x_1150_, v_k_1148_, v_v_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1152_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(lean_object* v_x_1153_, size_t v_x_1154_, size_t v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
lean_object* v_es_1158_; size_t v___x_1159_; size_t v___x_1160_; lean_object* v_j_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_es_1158_ = lean_ctor_get(v_x_1153_, 0);
v___x_1159_ = ((size_t)31ULL);
v___x_1160_ = lean_usize_land(v_x_1154_, v___x_1159_);
v_j_1161_ = lean_usize_to_nat(v___x_1160_);
v___x_1162_ = lean_array_get_size(v_es_1158_);
v___x_1163_ = lean_nat_dec_lt(v_j_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec(v_j_1161_);
lean_dec(v_x_1157_);
lean_dec(v_x_1156_);
return v_x_1153_;
}
else
{
lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1202_; 
lean_inc_ref(v_es_1158_);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1153_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_x_1153_, 0);
lean_dec(v_unused_1203_);
v___x_1165_ = v_x_1153_;
v_isShared_1166_ = v_isSharedCheck_1202_;
goto v_resetjp_1164_;
}
else
{
lean_dec(v_x_1153_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1202_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_v_1167_; lean_object* v___x_1168_; lean_object* v_xs_x27_1169_; lean_object* v___y_1171_; 
v_v_1167_ = lean_array_fget(v_es_1158_, v_j_1161_);
v___x_1168_ = lean_box(0);
v_xs_x27_1169_ = lean_array_fset(v_es_1158_, v_j_1161_, v___x_1168_);
switch(lean_obj_tag(v_v_1167_))
{
case 0:
{
lean_object* v_key_1176_; lean_object* v_val_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1187_; 
v_key_1176_ = lean_ctor_get(v_v_1167_, 0);
v_val_1177_ = lean_ctor_get(v_v_1167_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_v_1167_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1179_ = v_v_1167_;
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_val_1177_);
lean_inc(v_key_1176_);
lean_dec(v_v_1167_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint8_t v___x_1181_; 
v___x_1181_ = l_Lean_instBEqMVarId_beq(v_x_1156_, v_key_1176_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_del_object(v___x_1179_);
v___x_1182_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1176_, v_val_1177_, v_x_1156_, v_x_1157_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
v___y_1171_ = v___x_1183_;
goto v___jp_1170_;
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_val_1177_);
lean_dec(v_key_1176_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v_x_1157_);
lean_ctor_set(v___x_1179_, 0, v_x_1156_);
v___x_1185_ = v___x_1179_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_x_1156_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_x_1157_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
v___y_1171_ = v___x_1185_;
goto v___jp_1170_;
}
}
}
}
case 1:
{
lean_object* v_node_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1200_; 
v_node_1188_ = lean_ctor_get(v_v_1167_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_v_1167_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1190_ = v_v_1167_;
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_node_1188_);
lean_dec(v_v_1167_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
size_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1192_ = ((size_t)5ULL);
v___x_1193_ = lean_usize_shift_right(v_x_1154_, v___x_1192_);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_x_1155_, v___x_1194_);
v___x_1196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_node_1188_, v___x_1193_, v___x_1195_, v_x_1156_, v_x_1157_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1196_);
v___x_1198_ = v___x_1190_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
v___y_1171_ = v___x_1198_;
goto v___jp_1170_;
}
}
}
default: 
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_x_1156_);
lean_ctor_set(v___x_1201_, 1, v_x_1157_);
v___y_1171_ = v___x_1201_;
goto v___jp_1170_;
}
}
v___jp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_array_fset(v_xs_x27_1169_, v_j_1161_, v___y_1171_);
lean_dec(v_j_1161_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1172_);
v___x_1174_ = v___x_1165_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
else
{
lean_object* v_ks_1204_; lean_object* v_vs_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1223_; 
v_ks_1204_ = lean_ctor_get(v_x_1153_, 0);
v_vs_1205_ = lean_ctor_get(v_x_1153_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1153_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1207_ = v_x_1153_;
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_vs_1205_);
lean_inc(v_ks_1204_);
lean_dec(v_x_1153_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_ks_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_vs_1205_);
v___x_1210_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v_newNode_1211_; size_t v___x_1212_; uint8_t v___x_1213_; 
v_newNode_1211_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v___x_1210_, v_x_1156_, v_x_1157_);
v___x_1212_ = ((size_t)7ULL);
v___x_1213_ = lean_usize_dec_le(v___x_1212_, v_x_1155_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1211_);
v___x_1215_ = lean_unsigned_to_nat(4u);
v___x_1216_ = lean_nat_dec_lt(v___x_1214_, v___x_1215_);
lean_dec(v___x_1214_);
if (v___x_1216_ == 0)
{
lean_object* v_ks_1217_; lean_object* v_vs_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_ks_1217_ = lean_ctor_get(v_newNode_1211_, 0);
lean_inc_ref(v_ks_1217_);
v_vs_1218_ = lean_ctor_get(v_newNode_1211_, 1);
lean_inc_ref(v_vs_1218_);
lean_dec_ref(v_newNode_1211_);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0);
v___x_1221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_x_1155_, v_ks_1217_, v_vs_1218_, v___x_1219_, v___x_1220_);
lean_dec_ref(v_vs_1218_);
lean_dec_ref(v_ks_1217_);
return v___x_1221_;
}
else
{
return v_newNode_1211_;
}
}
else
{
return v_newNode_1211_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1153_ = stack[0].m_obj;
size_t v_x_1154_ = stack[1].m_num;
size_t v_x_1155_ = stack[2].m_num;
lean_object* v_x_1156_ = stack[3].m_obj;
lean_object* v_x_1157_ = stack[4].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1153_, v_x_1154_, v_x_1155_, v_x_1156_, v_x_1157_);
stack->m_obj
 = v_res_1224_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(size_t v_depth_1225_, lean_object* v_keys_1226_, lean_object* v_vals_1227_, lean_object* v_i_1228_, lean_object* v_entries_1229_){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_array_get_size(v_keys_1226_);
v___x_1231_ = lean_nat_dec_lt(v_i_1228_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_i_1228_);
return v_entries_1229_;
}
else
{
lean_object* v_k_1232_; lean_object* v_v_1233_; uint64_t v___x_1234_; size_t v_h_1235_; size_t v___x_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v_h_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_k_1232_ = lean_array_fget_borrowed(v_keys_1226_, v_i_1228_);
v_v_1233_ = lean_array_fget_borrowed(v_vals_1227_, v_i_1228_);
v___x_1234_ = l_Lean_instHashableMVarId_hash(v_k_1232_);
v_h_1235_ = lean_uint64_to_usize(v___x_1234_);
v___x_1236_ = ((size_t)5ULL);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_sub(v_depth_1225_, v___x_1238_);
v___x_1240_ = lean_usize_mul(v___x_1236_, v___x_1239_);
v_h_1241_ = lean_usize_shift_right(v_h_1235_, v___x_1240_);
v___x_1242_ = lean_nat_add(v_i_1228_, v___x_1237_);
lean_dec(v_i_1228_);
lean_inc(v_v_1233_);
lean_inc(v_k_1232_);
v___x_1243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_entries_1229_, v_h_1241_, v_depth_1225_, v_k_1232_, v_v_1233_);
v_i_1228_ = v___x_1242_;
v_entries_1229_ = v___x_1243_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1225_ = stack[0].m_num;
lean_object* v_keys_1226_ = stack[1].m_obj;
lean_object* v_vals_1227_ = stack[2].m_obj;
lean_object* v_i_1228_ = stack[3].m_obj;
lean_object* v_entries_1229_ = stack[4].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_1225_, v_keys_1226_, v_vals_1227_, v_i_1228_, v_entries_1229_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_depth_1246_, lean_object* v_keys_1247_, lean_object* v_vals_1248_, lean_object* v_i_1249_, lean_object* v_entries_1250_){
_start:
{
size_t v_depth_boxed_1251_; lean_object* v_res_1252_; 
v_depth_boxed_1251_ = lean_unbox_usize(v_depth_1246_);
lean_dec(v_depth_1246_);
v_res_1252_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_boxed_1251_, v_keys_1247_, v_vals_1248_, v_i_1249_, v_entries_1250_);
lean_dec_ref(v_vals_1248_);
lean_dec_ref(v_keys_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
size_t v_x_17201__boxed_1258_; size_t v_x_17202__boxed_1259_; lean_object* v_res_1260_; 
v_x_17201__boxed_1258_ = lean_unbox_usize(v_x_1254_);
lean_dec(v_x_1254_);
v_x_17202__boxed_1259_ = lean_unbox_usize(v_x_1255_);
lean_dec(v_x_1255_);
v_res_1260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1253_, v_x_17201__boxed_1258_, v_x_17202__boxed_1259_, v_x_1256_, v_x_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
uint64_t v___x_1264_; size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1264_ = l_Lean_instHashableMVarId_hash(v_x_1262_);
v___x_1265_ = lean_uint64_to_usize(v___x_1264_);
v___x_1266_ = ((size_t)1ULL);
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_1261_, v___x_1265_, v___x_1266_, v_x_1262_, v_x_1263_);
return v___x_1267_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(lean_object* v_mvarId_1268_, lean_object* v_val_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v_mctx_1273_; lean_object* v_cache_1274_; lean_object* v_zetaDeltaFVarIds_1275_; lean_object* v_postponed_1276_; lean_object* v_diag_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1307_; 
v___x_1272_ = lean_st_ref_take(v___y_1270_);
v_mctx_1273_ = lean_ctor_get(v___x_1272_, 0);
v_cache_1274_ = lean_ctor_get(v___x_1272_, 1);
v_zetaDeltaFVarIds_1275_ = lean_ctor_get(v___x_1272_, 2);
v_postponed_1276_ = lean_ctor_get(v___x_1272_, 3);
v_diag_1277_ = lean_ctor_get(v___x_1272_, 4);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1279_ = v___x_1272_;
v_isShared_1280_ = v_isSharedCheck_1307_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_diag_1277_);
lean_inc(v_postponed_1276_);
lean_inc(v_zetaDeltaFVarIds_1275_);
lean_inc(v_cache_1274_);
lean_inc(v_mctx_1273_);
lean_dec(v___x_1272_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1307_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_depth_1281_; lean_object* v_levelAssignDepth_1282_; lean_object* v_lmvarCounter_1283_; lean_object* v_mvarCounter_1284_; lean_object* v_lDecls_1285_; lean_object* v_decls_1286_; lean_object* v_userNames_1287_; lean_object* v_lAssignment_1288_; lean_object* v_eAssignment_1289_; lean_object* v_dAssignment_1290_; lean_object* v_instanceTypedMVars_1291_; lean_object* v_synthNormMemo_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1306_; 
v_depth_1281_ = lean_ctor_get(v_mctx_1273_, 0);
v_levelAssignDepth_1282_ = lean_ctor_get(v_mctx_1273_, 1);
v_lmvarCounter_1283_ = lean_ctor_get(v_mctx_1273_, 2);
v_mvarCounter_1284_ = lean_ctor_get(v_mctx_1273_, 3);
v_lDecls_1285_ = lean_ctor_get(v_mctx_1273_, 4);
v_decls_1286_ = lean_ctor_get(v_mctx_1273_, 5);
v_userNames_1287_ = lean_ctor_get(v_mctx_1273_, 6);
v_lAssignment_1288_ = lean_ctor_get(v_mctx_1273_, 7);
v_eAssignment_1289_ = lean_ctor_get(v_mctx_1273_, 8);
v_dAssignment_1290_ = lean_ctor_get(v_mctx_1273_, 9);
v_instanceTypedMVars_1291_ = lean_ctor_get(v_mctx_1273_, 10);
v_synthNormMemo_1292_ = lean_ctor_get(v_mctx_1273_, 11);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_mctx_1273_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1294_ = v_mctx_1273_;
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_synthNormMemo_1292_);
lean_inc(v_instanceTypedMVars_1291_);
lean_inc(v_dAssignment_1290_);
lean_inc(v_eAssignment_1289_);
lean_inc(v_lAssignment_1288_);
lean_inc(v_userNames_1287_);
lean_inc(v_decls_1286_);
lean_inc(v_lDecls_1285_);
lean_inc(v_mvarCounter_1284_);
lean_inc(v_lmvarCounter_1283_);
lean_inc(v_levelAssignDepth_1282_);
lean_inc(v_depth_1281_);
lean_dec(v_mctx_1273_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_eAssignment_1289_, v_mvarId_1268_, v_val_1269_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 8, v___x_1297_);
v___x_1299_ = v___x_1294_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_depth_1281_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_levelAssignDepth_1282_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_lmvarCounter_1283_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_mvarCounter_1284_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_lDecls_1285_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_decls_1286_);
lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_userNames_1287_);
lean_ctor_set(v_reuseFailAlloc_1305_, 7, v_lAssignment_1288_);
lean_ctor_set(v_reuseFailAlloc_1305_, 8, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1305_, 9, v_dAssignment_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 10, v_instanceTypedMVars_1291_);
lean_ctor_set(v_reuseFailAlloc_1305_, 11, v_synthNormMemo_1292_);
v___x_1299_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1299_);
v___x_1301_ = v___x_1279_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_cache_1274_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_zetaDeltaFVarIds_1275_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v_postponed_1276_);
lean_ctor_set(v_reuseFailAlloc_1304_, 4, v_diag_1277_);
v___x_1301_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_st_ref_put(v___y_1270_, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1296_);
return v___x_1303_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1268_ = stack[0].m_obj;
lean_object* v_val_1269_ = stack[1].m_obj;
lean_object* v___y_1270_ = stack[2].m_obj;
lean_object* v_res_1308_;
v_res_1308_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_1268_, v_val_1269_, v___y_1270_);
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(lean_object* v_mvarId_1309_, lean_object* v_val_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_1309_, v_val_1310_, v___y_1311_);
lean_dec(v___y_1311_);
return v_res_1313_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_k_1314_, lean_object* v_b_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
lean_inc_ref(v___y_1316_);
v___x_1321_ = lean_apply_6(v_k_1314_, v_b_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, lean_box(0));
return v___x_1321_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1314_ = stack[0].m_obj;
lean_object* v_b_1315_ = stack[1].m_obj;
lean_object* v___y_1316_ = stack[2].m_obj;
lean_object* v___y_1317_ = stack[3].m_obj;
lean_object* v___y_1318_ = stack[4].m_obj;
lean_object* v___y_1319_ = stack[5].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_1314_, v_b_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_k_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_1323_, v_b_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(lean_object* v_name_1331_, uint8_t v_bi_1332_, lean_object* v_type_1333_, lean_object* v_k_1334_, uint8_t v_kind_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___f_1341_; lean_object* v___x_1342_; 
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1341_, 0, v_k_1334_);
v___x_1342_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1331_, v_bi_1332_, v_type_1333_, v___f_1341_, v_kind_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1342_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1342_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1331_ = stack[0].m_obj;
uint8_t v_bi_1332_ = stack[1].m_num;
lean_object* v_type_1333_ = stack[2].m_obj;
lean_object* v_k_1334_ = stack[3].m_obj;
uint8_t v_kind_1335_ = stack[4].m_num;
lean_object* v___y_1336_ = stack[5].m_obj;
lean_object* v___y_1337_ = stack[6].m_obj;
lean_object* v___y_1338_ = stack[7].m_obj;
lean_object* v___y_1339_ = stack[8].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1331_, v_bi_1332_, v_type_1333_, v_k_1334_, v_kind_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_name_1360_, lean_object* v_bi_1361_, lean_object* v_type_1362_, lean_object* v_k_1363_, lean_object* v_kind_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_bi_boxed_1370_; uint8_t v_kind_boxed_1371_; lean_object* v_res_1372_; 
v_bi_boxed_1370_ = lean_unbox(v_bi_1361_);
v_kind_boxed_1371_ = lean_unbox(v_kind_1364_);
v_res_1372_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1360_, v_bi_boxed_1370_, v_type_1362_, v_k_1363_, v_kind_boxed_1371_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1372_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(lean_object* v_name_1373_, lean_object* v_type_1374_, lean_object* v_k_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
uint8_t v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = 0;
v___x_1382_ = 0;
v___x_1383_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_1373_, v___x_1381_, v_type_1374_, v_k_1375_, v___x_1382_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1383_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1373_ = stack[0].m_obj;
lean_object* v_type_1374_ = stack[1].m_obj;
lean_object* v_k_1375_ = stack[2].m_obj;
lean_object* v___y_1376_ = stack[3].m_obj;
lean_object* v___y_1377_ = stack[4].m_obj;
lean_object* v___y_1378_ = stack[5].m_obj;
lean_object* v___y_1379_ = stack[6].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_1373_, v_type_1374_, v_k_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(lean_object* v_name_1385_, lean_object* v_type_1386_, lean_object* v_k_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_1385_, v_type_1386_, v_k_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1393_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(lean_object* v_msgData_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; lean_object* v_env_1401_; uint8_t v___x_1402_; lean_object* v_env_1403_; lean_object* v___x_1404_; lean_object* v_toCold_1405_; lean_object* v_mctx_1406_; lean_object* v_lctx_1407_; lean_object* v_options_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1400_ = lean_st_ref_get(v___y_1398_);
v_env_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc_ref(v_env_1401_);
lean_dec(v___x_1400_);
v___x_1402_ = 0;
v_env_1403_ = l_Lean_Environment_setRecordingDeps(v_env_1401_, v___x_1402_);
v___x_1404_ = lean_st_ref_get(v___y_1396_);
v_toCold_1405_ = lean_ctor_get(v___y_1397_, 0);
v_mctx_1406_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_mctx_1406_);
lean_dec(v___x_1404_);
v_lctx_1407_ = lean_ctor_get(v___y_1395_, 2);
v_options_1408_ = lean_ctor_get(v_toCold_1405_, 2);
lean_inc_ref(v_options_1408_);
lean_inc_ref(v_lctx_1407_);
v___x_1409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1409_, 0, v_env_1403_);
lean_ctor_set(v___x_1409_, 1, v_mctx_1406_);
lean_ctor_set(v___x_1409_, 2, v_lctx_1407_);
lean_ctor_set(v___x_1409_, 3, v_options_1408_);
v___x_1410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_msgData_1394_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1394_ = stack[0].m_obj;
lean_object* v___y_1395_ = stack[1].m_obj;
lean_object* v___y_1396_ = stack[2].m_obj;
lean_object* v___y_1397_ = stack[3].m_obj;
lean_object* v___y_1398_ = stack[4].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1419_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(lean_object* v_msg_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_ref_1426_; lean_object* v___x_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_ref_1426_ = lean_ctor_get(v___y_1423_, 2);
v___x_1427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msg_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_inc(v_ref_1426_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_ref_1426_);
lean_ctor_set(v___x_1432_, 1, v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 1);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1420_ = stack[0].m_obj;
lean_object* v___y_1421_ = stack[1].m_obj;
lean_object* v___y_1422_ = stack[2].m_obj;
lean_object* v___y_1423_ = stack[3].m_obj;
lean_object* v___y_1424_ = stack[4].m_obj;
lean_object* v_res_1437_;
v_res_1437_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
stack->m_obj
 = v_res_1437_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1444_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(lean_object* v___x_1445_, lean_object* v_ident_1446_, uint8_t v___x_1447_, lean_object* v_hyps_1448_, lean_object* v___x_1449_, lean_object* v_target_1450_, lean_object* v_u_1451_, lean_object* v_k_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v_s_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_lctx_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_lctx_1463_ = lean_ctor_get(v___y_1458_, 2);
lean_inc_ref(v___x_1445_);
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1445_);
lean_inc_ref(v_s_1457_);
lean_inc_ref(v_lctx_1463_);
v___x_1465_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_ident_1446_, v_lctx_1463_, v_s_1457_, v___x_1464_, v___x_1447_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref_known(v___x_1465_, 1);
lean_inc_ref(v_s_1457_);
lean_inc_ref(v_hyps_1448_);
v___x_1466_ = l_Lean_Expr_app___override(v_hyps_1448_, v_s_1457_);
lean_inc_ref_n(v___x_1449_, 2);
v___x_1467_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___x_1449_, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_mk_empty_array_with_capacity(v___x_1468_);
v___x_1470_ = lean_array_push(v___x_1469_, v_s_1457_);
v___x_1471_ = 0;
lean_inc_ref(v_target_1450_);
v___x_1472_ = l_Lean_Expr_betaRev(v_target_1450_, v___x_1470_, v___x_1471_, v___x_1471_);
lean_inc(v_u_1451_);
v___x_1473_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1473_, 0, v_u_1451_);
lean_ctor_set(v___x_1473_, 1, v___x_1449_);
lean_ctor_set(v___x_1473_, 2, v___x_1467_);
lean_ctor_set(v___x_1473_, 3, v___x_1472_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
v___x_1474_ = lean_apply_10(v_k_1452_, v___x_1473_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, lean_box(0));
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = 1;
v___x_1477_ = l_Lean_Meta_mkLambdaFVars(v___x_1470_, v_a_1475_, v___x_1471_, v___x_1447_, v___x_1471_, v___x_1447_, v___x_1476_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec_ref(v___x_1470_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1490_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1482_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1));
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_u_1451_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_mkConst(v___x_1482_, v___x_1484_);
v___x_1486_ = l_Lean_mkApp5(v___x_1485_, v___x_1449_, v___x_1445_, v_hyps_1448_, v_target_1450_, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1486_);
v___x_1488_ = v___x_1480_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_dec(v_u_1451_);
lean_dec_ref(v_target_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_hyps_1448_);
lean_dec_ref(v___x_1445_);
return v___x_1477_;
}
}
else
{
lean_dec_ref(v___x_1470_);
lean_dec(v_u_1451_);
lean_dec_ref(v_target_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_hyps_1448_);
lean_dec_ref(v___x_1445_);
return v___x_1474_;
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_s_1457_);
lean_dec_ref(v_k_1452_);
lean_dec(v_u_1451_);
lean_dec_ref(v_target_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_hyps_1448_);
lean_dec_ref(v___x_1445_);
v_a_1491_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1465_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1465_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1445_ = stack[0].m_obj;
lean_object* v_ident_1446_ = stack[1].m_obj;
uint8_t v___x_1447_ = stack[2].m_num;
lean_object* v_hyps_1448_ = stack[3].m_obj;
lean_object* v___x_1449_ = stack[4].m_obj;
lean_object* v_target_1450_ = stack[5].m_obj;
lean_object* v_u_1451_ = stack[6].m_obj;
lean_object* v_k_1452_ = stack[7].m_obj;
lean_object* v___y_1453_ = stack[8].m_obj;
lean_object* v___y_1454_ = stack[9].m_obj;
lean_object* v___y_1455_ = stack[10].m_obj;
lean_object* v___y_1456_ = stack[11].m_obj;
lean_object* v_s_1457_ = stack[12].m_obj;
lean_object* v___y_1458_ = stack[13].m_obj;
lean_object* v___y_1459_ = stack[14].m_obj;
lean_object* v___y_1460_ = stack[15].m_obj;
lean_object* v___y_1461_ = stack[16].m_obj;
lean_object* v_res_1499_;
v_res_1499_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_1445_, v_ident_1446_, v___x_1447_, v_hyps_1448_, v___x_1449_, v_target_1450_, v_u_1451_, v_k_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v_s_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
stack->m_obj
 = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_1500_ = _args[0];
lean_object* v_ident_1501_ = _args[1];
lean_object* v___x_1502_ = _args[2];
lean_object* v_hyps_1503_ = _args[3];
lean_object* v___x_1504_ = _args[4];
lean_object* v_target_1505_ = _args[5];
lean_object* v_u_1506_ = _args[6];
lean_object* v_k_1507_ = _args[7];
lean_object* v___y_1508_ = _args[8];
lean_object* v___y_1509_ = _args[9];
lean_object* v___y_1510_ = _args[10];
lean_object* v___y_1511_ = _args[11];
lean_object* v_s_1512_ = _args[12];
lean_object* v___y_1513_ = _args[13];
lean_object* v___y_1514_ = _args[14];
lean_object* v___y_1515_ = _args[15];
lean_object* v___y_1516_ = _args[16];
lean_object* v___y_1517_ = _args[17];
_start:
{
uint8_t v___x_17774__boxed_1518_; lean_object* v_res_1519_; 
v___x_17774__boxed_1518_ = lean_unbox(v___x_1502_);
v_res_1519_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_1500_, v_ident_1501_, v___x_17774__boxed_1518_, v_hyps_1503_, v___x_1504_, v_target_1505_, v_u_1506_, v_k_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v_s_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1519_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(lean_object* v_goal_1520_, lean_object* v_ident_1521_, lean_object* v_k_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___y_1533_; lean_object* v_u_1542_; lean_object* v_00_u03c3s_1543_; lean_object* v_hyps_1544_; lean_object* v_target_1545_; lean_object* v___x_1546_; 
v_u_1542_ = lean_ctor_get(v_goal_1520_, 0);
lean_inc(v_u_1542_);
v_00_u03c3s_1543_ = lean_ctor_get(v_goal_1520_, 1);
lean_inc_ref_n(v_00_u03c3s_1543_, 2);
v_hyps_1544_ = lean_ctor_get(v_goal_1520_, 2);
lean_inc_ref(v_hyps_1544_);
v_target_1545_ = lean_ctor_get(v_goal_1520_, 3);
lean_inc_ref(v_target_1545_);
lean_dec_ref(v_goal_1520_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
lean_inc(v___y_1528_);
lean_inc_ref(v___y_1527_);
v___x_1546_ = lean_whnf(v_00_u03c3s_1543_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2));
v___x_1549_ = lean_unsigned_to_nat(3u);
v___x_1550_ = l_Lean_Expr_isAppOfArity(v_a_1547_, v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v_a_1547_);
lean_dec_ref(v_target_1545_);
lean_dec_ref(v_hyps_1544_);
lean_dec(v_u_1542_);
lean_dec_ref(v_k_1522_);
lean_dec(v_ident_1521_);
v___x_1551_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
v___x_1552_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_1543_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1553_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
v___y_1533_ = v___x_1554_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
lean_dec_ref(v_00_u03c3s_1543_);
v___x_1555_ = l_Lean_Expr_appFn_x21(v_a_1547_);
v___x_1556_ = l_Lean_Expr_appArg_x21(v___x_1555_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = l_Lean_Expr_appArg_x21(v_a_1547_);
lean_dec(v_a_1547_);
v___x_1558_ = lean_box(v___x_1550_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
lean_inc_n(v_ident_1521_, 2);
lean_inc_ref(v___x_1556_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1559_, 0, v___x_1556_);
lean_closure_set(v___f_1559_, 1, v_ident_1521_);
lean_closure_set(v___f_1559_, 2, v___x_1558_);
lean_closure_set(v___f_1559_, 3, v_hyps_1544_);
lean_closure_set(v___f_1559_, 4, v___x_1557_);
lean_closure_set(v___f_1559_, 5, v_target_1545_);
lean_closure_set(v___f_1559_, 6, v_u_1542_);
lean_closure_set(v___f_1559_, 7, v_k_1522_);
lean_closure_set(v___f_1559_, 8, v___y_1523_);
lean_closure_set(v___f_1559_, 9, v___y_1524_);
lean_closure_set(v___f_1559_, 10, v___y_1525_);
lean_closure_set(v___f_1559_, 11, v___y_1526_);
v___x_1560_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
v___x_1561_ = l_Lean_Syntax_isOfKind(v_ident_1521_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_ident_1521_);
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1563_ = l_Lean_Core_mkFreshUserName(v___x_1562_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1564_, v___x_1556_, v___f_1559_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
v___y_1533_ = v___x_1565_;
goto v___jp_1532_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v___f_1559_);
lean_dec_ref(v___x_1556_);
v_a_1566_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1563_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1563_);
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
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = l_Lean_Syntax_getArg(v_ident_1521_, v___x_1574_);
lean_dec(v_ident_1521_);
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v___x_1575_);
v___x_1577_ = l_Lean_Syntax_isOfKind(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v___x_1575_);
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6));
v___x_1579_ = l_Lean_Core_mkFreshUserName(v___x_1578_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_1580_, v___x_1556_, v___f_1559_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
v___y_1533_ = v___x_1581_;
goto v___jp_1532_;
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___f_1559_);
lean_dec_ref(v___x_1556_);
v_a_1582_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1579_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1579_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = l_Lean_TSyntax_getId(v___x_1575_);
lean_dec(v___x_1575_);
v___x_1591_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v___x_1590_, v___x_1556_, v___f_1559_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
v___y_1533_ = v___x_1591_;
goto v___jp_1532_;
}
}
}
}
else
{
lean_dec_ref(v_target_1545_);
lean_dec_ref(v_hyps_1544_);
lean_dec_ref(v_00_u03c3s_1543_);
lean_dec(v_u_1542_);
lean_dec_ref(v_k_1522_);
lean_dec(v_ident_1521_);
return v___x_1546_;
}
v___jp_1532_:
{
if (lean_obj_tag(v___y_1533_) == 0)
{
return v___y_1533_;
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v___y_1533_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___y_1533_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___y_1533_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___y_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1520_ = stack[0].m_obj;
lean_object* v_ident_1521_ = stack[1].m_obj;
lean_object* v_k_1522_ = stack[2].m_obj;
lean_object* v___y_1523_ = stack[3].m_obj;
lean_object* v___y_1524_ = stack[4].m_obj;
lean_object* v___y_1525_ = stack[5].m_obj;
lean_object* v___y_1526_ = stack[6].m_obj;
lean_object* v___y_1527_ = stack[7].m_obj;
lean_object* v___y_1528_ = stack[8].m_obj;
lean_object* v___y_1529_ = stack[9].m_obj;
lean_object* v___y_1530_ = stack[10].m_obj;
lean_object* v_res_1592_;
v_res_1592_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_1520_, v_ident_1521_, v_k_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
stack->m_obj
 = v_res_1592_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(lean_object* v_goal_1593_, lean_object* v_ident_1594_, lean_object* v_k_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_1593_, v_ident_1594_, v_k_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1605_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(lean_object* v___x_1606_, lean_object* v_snd_1607_, lean_object* v_ident_1608_, lean_object* v_fst_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_st_mk_ref(v___x_1606_);
lean_inc(v___x_1619_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1620_, 0, v___x_1619_);
v___x_1621_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_snd_1607_, v_ident_1608_, v___f_1620_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1609_, v_a_1622_, v___y_1615_);
lean_dec_ref(v___x_1623_);
v___x_1624_ = lean_st_ref_get(v___x_1619_);
lean_dec(v___x_1619_);
v___x_1625_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1624_, v___y_1611_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1625_;
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v___x_1619_);
lean_dec(v_fst_1609_);
v_a_1626_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1621_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1621_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1606_ = stack[0].m_obj;
lean_object* v_snd_1607_ = stack[1].m_obj;
lean_object* v_ident_1608_ = stack[2].m_obj;
lean_object* v_fst_1609_ = stack[3].m_obj;
lean_object* v___y_1610_ = stack[4].m_obj;
lean_object* v___y_1611_ = stack[5].m_obj;
lean_object* v___y_1612_ = stack[6].m_obj;
lean_object* v___y_1613_ = stack[7].m_obj;
lean_object* v___y_1614_ = stack[8].m_obj;
lean_object* v___y_1615_ = stack[9].m_obj;
lean_object* v___y_1616_ = stack[10].m_obj;
lean_object* v___y_1617_ = stack[11].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(v___x_1606_, v_snd_1607_, v_ident_1608_, v_fst_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(lean_object* v___x_1635_, lean_object* v_snd_1636_, lean_object* v_ident_1637_, lean_object* v_fst_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(v___x_1635_, v_snd_1636_, v_ident_1637_, v_fst_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1648_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(lean_object* v_k_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v_b_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
v___x_1660_ = lean_apply_10(v_k_1649_, v_b_1654_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, lean_box(0));
return v___x_1660_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1649_ = stack[0].m_obj;
lean_object* v___y_1650_ = stack[1].m_obj;
lean_object* v___y_1651_ = stack[2].m_obj;
lean_object* v___y_1652_ = stack[3].m_obj;
lean_object* v___y_1653_ = stack[4].m_obj;
lean_object* v_b_1654_ = stack[5].m_obj;
lean_object* v___y_1655_ = stack[6].m_obj;
lean_object* v___y_1656_ = stack[7].m_obj;
lean_object* v___y_1657_ = stack[8].m_obj;
lean_object* v___y_1658_ = stack[9].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v_b_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(lean_object* v_k_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v_b_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v_b_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1673_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(lean_object* v_name_1674_, lean_object* v_type_1675_, lean_object* v_val_1676_, lean_object* v_k_1677_, uint8_t v_nondep_1678_, uint8_t v_kind_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___f_1689_; lean_object* v___x_1690_; 
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1689_, 0, v_k_1677_);
lean_closure_set(v___f_1689_, 1, v___y_1680_);
lean_closure_set(v___f_1689_, 2, v___y_1681_);
lean_closure_set(v___f_1689_, 3, v___y_1682_);
lean_closure_set(v___f_1689_, 4, v___y_1683_);
v___x_1690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1674_, v_type_1675_, v_val_1676_, v___f_1689_, v_nondep_1678_, v_kind_1679_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
return v___x_1690_;
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
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
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1674_ = stack[0].m_obj;
lean_object* v_type_1675_ = stack[1].m_obj;
lean_object* v_val_1676_ = stack[2].m_obj;
lean_object* v_k_1677_ = stack[3].m_obj;
uint8_t v_nondep_1678_ = stack[4].m_num;
uint8_t v_kind_1679_ = stack[5].m_num;
lean_object* v___y_1680_ = stack[6].m_obj;
lean_object* v___y_1681_ = stack[7].m_obj;
lean_object* v___y_1682_ = stack[8].m_obj;
lean_object* v___y_1683_ = stack[9].m_obj;
lean_object* v___y_1684_ = stack[10].m_obj;
lean_object* v___y_1685_ = stack[11].m_obj;
lean_object* v___y_1686_ = stack[12].m_obj;
lean_object* v___y_1687_ = stack[13].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1674_, v_type_1675_, v_val_1676_, v_k_1677_, v_nondep_1678_, v_kind_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(lean_object* v_name_1700_, lean_object* v_type_1701_, lean_object* v_val_1702_, lean_object* v_k_1703_, lean_object* v_nondep_1704_, lean_object* v_kind_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_nondep_boxed_1715_; uint8_t v_kind_boxed_1716_; lean_object* v_res_1717_; 
v_nondep_boxed_1715_ = lean_unbox(v_nondep_1704_);
v_kind_boxed_1716_ = lean_unbox(v_kind_1705_);
v_res_1717_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1700_, v_type_1701_, v_val_1702_, v_k_1703_, v_nondep_boxed_1715_, v_kind_boxed_1716_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1717_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v_ngen_1721_; lean_object* v_namePrefix_1722_; lean_object* v_idx_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1753_; 
v___x_1720_ = lean_st_ref_get(v___y_1718_);
v_ngen_1721_ = lean_ctor_get(v___x_1720_, 2);
lean_inc_ref(v_ngen_1721_);
lean_dec(v___x_1720_);
v_namePrefix_1722_ = lean_ctor_get(v_ngen_1721_, 0);
v_idx_1723_ = lean_ctor_get(v_ngen_1721_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_ngen_1721_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1725_ = v_ngen_1721_;
v_isShared_1726_ = v_isSharedCheck_1753_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_idx_1723_);
lean_inc(v_namePrefix_1722_);
lean_dec(v_ngen_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1753_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_r_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_inc(v_idx_1723_);
lean_inc(v_namePrefix_1722_);
v_r_1727_ = l_Lean_Name_num___override(v_namePrefix_1722_, v_idx_1723_);
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_add(v_idx_1723_, v___x_1728_);
lean_dec(v_idx_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1729_);
v___x_1731_ = v___x_1725_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_namePrefix_1722_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v_env_1733_; lean_object* v_nextMacroScope_1734_; lean_object* v_auxDeclNGen_1735_; lean_object* v_traceState_1736_; lean_object* v_cache_1737_; lean_object* v_recordedDeps_1738_; lean_object* v_messages_1739_; lean_object* v_infoState_1740_; lean_object* v_snapshotTasks_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1750_; 
v___x_1732_ = lean_st_ref_take(v___y_1718_);
v_env_1733_ = lean_ctor_get(v___x_1732_, 0);
v_nextMacroScope_1734_ = lean_ctor_get(v___x_1732_, 1);
v_auxDeclNGen_1735_ = lean_ctor_get(v___x_1732_, 3);
v_traceState_1736_ = lean_ctor_get(v___x_1732_, 4);
v_cache_1737_ = lean_ctor_get(v___x_1732_, 5);
v_recordedDeps_1738_ = lean_ctor_get(v___x_1732_, 6);
v_messages_1739_ = lean_ctor_get(v___x_1732_, 7);
v_infoState_1740_ = lean_ctor_get(v___x_1732_, 8);
v_snapshotTasks_1741_ = lean_ctor_get(v___x_1732_, 9);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1732_, 2);
lean_dec(v_unused_1751_);
v___x_1743_ = v___x_1732_;
v_isShared_1744_ = v_isSharedCheck_1750_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snapshotTasks_1741_);
lean_inc(v_infoState_1740_);
lean_inc(v_messages_1739_);
lean_inc(v_recordedDeps_1738_);
lean_inc(v_cache_1737_);
lean_inc(v_traceState_1736_);
lean_inc(v_auxDeclNGen_1735_);
lean_inc(v_nextMacroScope_1734_);
lean_inc(v_env_1733_);
lean_dec(v___x_1732_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1750_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 2, v___x_1731_);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_env_1733_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_nextMacroScope_1734_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_auxDeclNGen_1735_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_traceState_1736_);
lean_ctor_set(v_reuseFailAlloc_1749_, 5, v_cache_1737_);
lean_ctor_set(v_reuseFailAlloc_1749_, 6, v_recordedDeps_1738_);
lean_ctor_set(v_reuseFailAlloc_1749_, 7, v_messages_1739_);
lean_ctor_set(v_reuseFailAlloc_1749_, 8, v_infoState_1740_);
lean_ctor_set(v_reuseFailAlloc_1749_, 9, v_snapshotTasks_1741_);
v___x_1746_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_st_ref_put(v___y_1718_, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_r_1727_);
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1718_ = stack[0].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1718_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1755_);
lean_dec(v___y_1755_);
return v_res_1757_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(lean_object* v_body_1758_, lean_object* v_u_1759_, lean_object* v_00_u03c3s_1760_, lean_object* v_hyps_1761_, lean_object* v_k_1762_, lean_object* v_val_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_expr_instantiate1(v_body_1758_, v_val_1763_);
v___x_1774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1774_, 0, v_u_1759_);
lean_ctor_set(v___x_1774_, 1, v_00_u03c3s_1760_);
lean_ctor_set(v___x_1774_, 2, v_hyps_1761_);
lean_ctor_set(v___x_1774_, 3, v___x_1773_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
lean_inc(v___y_1769_);
lean_inc_ref(v___y_1768_);
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
v___x_1775_ = lean_apply_10(v_k_1762_, v___x_1774_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_mk_empty_array_with_capacity(v___x_1777_);
v___x_1779_ = lean_array_push(v___x_1778_, v_val_1763_);
v___x_1780_ = 1;
v___x_1781_ = 1;
v___x_1782_ = l_Lean_Meta_mkLetFVars(v___x_1779_, v_a_1776_, v___x_1780_, v___x_1780_, v___x_1781_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec_ref(v___x_1779_);
return v___x_1782_;
}
else
{
lean_dec_ref(v_val_1763_);
return v___x_1775_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_1758_ = stack[0].m_obj;
lean_object* v_u_1759_ = stack[1].m_obj;
lean_object* v_00_u03c3s_1760_ = stack[2].m_obj;
lean_object* v_hyps_1761_ = stack[3].m_obj;
lean_object* v_k_1762_ = stack[4].m_obj;
lean_object* v_val_1763_ = stack[5].m_obj;
lean_object* v___y_1764_ = stack[6].m_obj;
lean_object* v___y_1765_ = stack[7].m_obj;
lean_object* v___y_1766_ = stack[8].m_obj;
lean_object* v___y_1767_ = stack[9].m_obj;
lean_object* v___y_1768_ = stack[10].m_obj;
lean_object* v___y_1769_ = stack[11].m_obj;
lean_object* v___y_1770_ = stack[12].m_obj;
lean_object* v___y_1771_ = stack[13].m_obj;
lean_object* v_res_1783_;
v_res_1783_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_1758_, v_u_1759_, v_00_u03c3s_1760_, v_hyps_1761_, v_k_1762_, v_val_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
stack->m_obj
 = v_res_1783_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(lean_object* v_body_1784_, lean_object* v_u_1785_, lean_object* v_00_u03c3s_1786_, lean_object* v_hyps_1787_, lean_object* v_k_1788_, lean_object* v_val_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_1784_, v_u_1785_, v_00_u03c3s_1786_, v_hyps_1787_, v_k_1788_, v_val_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_body_1784_);
return v_res_1799_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(lean_object* v_goal_1807_, lean_object* v_ident_1808_, lean_object* v_k_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_u_1819_; lean_object* v_00_u03c3s_1820_; lean_object* v_hyps_1821_; lean_object* v_target_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1933_; 
v_u_1819_ = lean_ctor_get(v_goal_1807_, 0);
v_00_u03c3s_1820_ = lean_ctor_get(v_goal_1807_, 1);
v_hyps_1821_ = lean_ctor_get(v_goal_1807_, 2);
v_target_1822_ = lean_ctor_get(v_goal_1807_, 3);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_goal_1807_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1824_ = v_goal_1807_;
v_isShared_1825_ = v_isSharedCheck_1933_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_target_1822_);
lean_inc(v_hyps_1821_);
lean_inc(v_00_u03c3s_1820_);
lean_inc(v_u_1819_);
lean_dec(v_goal_1807_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1933_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24));
v___x_1827_ = lean_unsigned_to_nat(3u);
v___x_1828_ = l_Lean_Expr_isAppOfArity(v_target_1822_, v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_del_object(v___x_1824_);
if (lean_obj_tag(v_target_1822_) == 8)
{
lean_object* v_declName_1829_; lean_object* v_type_1830_; lean_object* v_value_1831_; lean_object* v_body_1832_; lean_object* v___f_1833_; lean_object* v_name_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v_declName_1829_ = lean_ctor_get(v_target_1822_, 0);
lean_inc(v_declName_1829_);
v_type_1830_ = lean_ctor_get(v_target_1822_, 1);
lean_inc_ref(v_type_1830_);
v_value_1831_ = lean_ctor_get(v_target_1822_, 2);
lean_inc_ref(v_value_1831_);
v_body_1832_ = lean_ctor_get(v_target_1822_, 3);
lean_inc_ref(v_body_1832_);
lean_dec_ref_known(v_target_1822_, 4);
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed), 15, 5);
lean_closure_set(v___f_1833_, 0, v_body_1832_);
lean_closure_set(v___f_1833_, 1, v_u_1819_);
lean_closure_set(v___f_1833_, 2, v_00_u03c3s_1820_);
lean_closure_set(v___f_1833_, 3, v_hyps_1821_);
lean_closure_set(v___f_1833_, 4, v_k_1809_);
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_1808_);
v___x_1847_ = l_Lean_Syntax_isOfKind(v_ident_1808_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_dec(v_ident_1808_);
v___x_1848_ = l_Lean_Core_mkFreshUserName(v_declName_1829_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v_name_1835_ = v_a_1849_;
v___y_1836_ = v___y_1810_;
v___y_1837_ = v___y_1811_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
goto v___jp_1834_;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v___f_1833_);
lean_dec_ref(v_value_1831_);
lean_dec_ref(v_type_1830_);
v_a_1850_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1848_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1848_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v_name_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v_name_1859_ = l_Lean_Syntax_getArg(v_ident_1808_, v___x_1858_);
lean_dec(v_ident_1808_);
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29));
lean_inc(v_name_1859_);
v___x_1861_ = l_Lean_Syntax_isOfKind(v_name_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v_name_1859_);
v___x_1862_ = l_Lean_Core_mkFreshUserName(v_declName_1829_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v_name_1835_ = v_a_1863_;
v___y_1836_ = v___y_1810_;
v___y_1837_ = v___y_1811_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
goto v___jp_1834_;
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec_ref(v___f_1833_);
lean_dec_ref(v_value_1831_);
lean_dec_ref(v_type_1830_);
v_a_1864_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1862_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1862_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v___x_1872_; 
lean_dec(v_declName_1829_);
v___x_1872_ = l_Lean_TSyntax_getId(v_name_1859_);
lean_dec(v_name_1859_);
v_name_1835_ = v___x_1872_;
v___y_1836_ = v___y_1810_;
v___y_1837_ = v___y_1811_;
v___y_1838_ = v___y_1812_;
v___y_1839_ = v___y_1813_;
v___y_1840_ = v___y_1814_;
v___y_1841_ = v___y_1815_;
v___y_1842_ = v___y_1816_;
v___y_1843_ = v___y_1817_;
goto v___jp_1834_;
}
}
v___jp_1834_:
{
uint8_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = 0;
v___x_1845_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_1835_, v_type_1830_, v_value_1831_, v___f_1833_, v___x_1828_, v___x_1844_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec_ref(v_hyps_1821_);
lean_dec_ref(v_00_u03c3s_1820_);
lean_dec(v_u_1819_);
lean_dec_ref(v_k_1809_);
lean_dec(v_ident_1808_);
v___x_1873_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31);
v___x_1874_ = l_Lean_MessageData_ofExpr(v_target_1822_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_1875_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1876_;
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1877_ = l_Lean_Expr_appFn_x21(v_target_1822_);
v___x_1878_ = l_Lean_Expr_appFn_x21(v___x_1877_);
v___x_1879_ = l_Lean_Expr_appArg_x21(v___x_1878_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = l_Lean_Expr_appArg_x21(v___x_1877_);
lean_dec_ref(v___x_1877_);
v___x_1881_ = l_Lean_Expr_appArg_x21(v_target_1822_);
lean_dec_ref(v_target_1822_);
v___x_1882_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_1808_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v___x_1886_; lean_object* v_a_1887_; lean_object* v_hyp_1888_; lean_object* v___x_1889_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v_fst_1884_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_fst_1884_);
v_snd_1885_ = lean_ctor_get(v_a_1883_, 1);
lean_inc(v_snd_1885_);
lean_dec(v_a_1883_);
v___x_1886_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_1817_);
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
v_hyp_1888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hyp_1888_, 0, v_fst_1884_);
lean_ctor_set(v_hyp_1888_, 1, v_a_1887_);
lean_ctor_set(v_hyp_1888_, 2, v___x_1880_);
lean_inc_ref(v_hyp_1888_);
lean_inc_ref(v___x_1879_);
v___x_1889_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1885_, v___x_1879_, v_hyp_1888_, v___x_1828_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_H_1890_; lean_object* v___x_1891_; lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref_known(v___x_1889_, 1);
v_H_1890_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_1888_);
lean_inc_ref(v_H_1890_);
lean_inc_ref(v_hyps_1821_);
lean_inc_ref(v_00_u03c3s_1820_);
lean_inc(v_u_1819_);
v___x_1891_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_1819_, v_00_u03c3s_1820_, v_hyps_1821_, v_H_1890_);
v_fst_1892_ = lean_ctor_get(v___x_1891_, 0);
v_snd_1893_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1895_ = v___x_1891_;
v_isShared_1896_ = v_isSharedCheck_1916_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snd_1893_);
lean_inc(v_fst_1892_);
lean_dec(v___x_1891_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1916_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
lean_inc_ref(v___x_1881_);
lean_inc(v_fst_1892_);
lean_inc(v_u_1819_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 3, v___x_1881_);
lean_ctor_set(v___x_1824_, 2, v_fst_1892_);
v___x_1898_ = v___x_1824_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_u_1819_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_00_u03c3s_1820_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_fst_1892_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v___x_1881_);
v___x_1898_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; 
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
v___x_1899_ = lean_apply_10(v_k_1809_, v___x_1898_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, lean_box(0));
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1914_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1914_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1914_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0));
v___x_1905_ = lean_box(0);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
lean_ctor_set(v___x_1895_, 1, v___x_1905_);
lean_ctor_set(v___x_1895_, 0, v_u_1819_);
v___x_1907_ = v___x_1895_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_u_1819_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v_prf_1909_; lean_object* v___x_1911_; 
v___x_1908_ = l_Lean_mkConst(v___x_1904_, v___x_1907_);
v_prf_1909_ = l_Lean_mkApp7(v___x_1908_, v___x_1879_, v_fst_1892_, v_hyps_1821_, v_H_1890_, v___x_1881_, v_snd_1893_, v_a_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_prf_1909_);
v___x_1911_ = v___x_1902_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_prf_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_del_object(v___x_1895_);
lean_dec(v_snd_1893_);
lean_dec(v_fst_1892_);
lean_dec_ref(v_H_1890_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_hyps_1821_);
lean_dec(v_u_1819_);
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref_known(v_hyp_1888_, 3);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1879_);
lean_del_object(v___x_1824_);
lean_dec_ref(v_hyps_1821_);
lean_dec_ref(v_00_u03c3s_1820_);
lean_dec(v_u_1819_);
lean_dec_ref(v_k_1809_);
v_a_1917_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1889_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1889_);
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
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1880_);
lean_dec_ref(v___x_1879_);
lean_del_object(v___x_1824_);
lean_dec_ref(v_hyps_1821_);
lean_dec_ref(v_00_u03c3s_1820_);
lean_dec(v_u_1819_);
lean_dec_ref(v_k_1809_);
v_a_1925_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1882_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1882_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1807_ = stack[0].m_obj;
lean_object* v_ident_1808_ = stack[1].m_obj;
lean_object* v_k_1809_ = stack[2].m_obj;
lean_object* v___y_1810_ = stack[3].m_obj;
lean_object* v___y_1811_ = stack[4].m_obj;
lean_object* v___y_1812_ = stack[5].m_obj;
lean_object* v___y_1813_ = stack[6].m_obj;
lean_object* v___y_1814_ = stack[7].m_obj;
lean_object* v___y_1815_ = stack[8].m_obj;
lean_object* v___y_1816_ = stack[9].m_obj;
lean_object* v___y_1817_ = stack[10].m_obj;
lean_object* v_res_1934_;
v_res_1934_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_1807_, v_ident_1808_, v_k_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
stack->m_obj
 = v_res_1934_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(lean_object* v_goal_1935_, lean_object* v_ident_1936_, lean_object* v_k_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_1935_, v_ident_1936_, v_k_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1947_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(lean_object* v___x_1948_, lean_object* v_snd_1949_, lean_object* v_ident_1950_, lean_object* v_fst_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_st_mk_ref(v___x_1948_);
lean_inc(v___x_1961_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1962_, 0, v___x_1961_);
v___x_1963_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_snd_1949_, v_ident_1950_, v___f_1962_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_1951_, v_a_1964_, v___y_1957_);
lean_dec_ref(v___x_1965_);
v___x_1966_ = lean_st_ref_get(v___x_1961_);
lean_dec(v___x_1961_);
v___x_1967_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1966_, v___y_1953_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1967_;
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v___x_1961_);
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1948_ = stack[0].m_obj;
lean_object* v_snd_1949_ = stack[1].m_obj;
lean_object* v_ident_1950_ = stack[2].m_obj;
lean_object* v_fst_1951_ = stack[3].m_obj;
lean_object* v___y_1952_ = stack[4].m_obj;
lean_object* v___y_1953_ = stack[5].m_obj;
lean_object* v___y_1954_ = stack[6].m_obj;
lean_object* v___y_1955_ = stack[7].m_obj;
lean_object* v___y_1956_ = stack[8].m_obj;
lean_object* v___y_1957_ = stack[9].m_obj;
lean_object* v___y_1958_ = stack[10].m_obj;
lean_object* v___y_1959_ = stack[11].m_obj;
lean_object* v_res_1976_;
v_res_1976_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(v___x_1948_, v_snd_1949_, v_ident_1950_, v_fst_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
stack->m_obj
 = v_res_1976_;
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(lean_object* v_x_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
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
lean_object* v_ident_2021_; 
v_ident_2021_ = l_Lean_Syntax_getArg(v___x_2015_, v___x_2010_);
lean_dec(v___x_2015_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_2021_);
v___x_2039_ = l_Lean_Syntax_isOfKind(v_ident_2021_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec(v_ident_2021_);
v___x_2040_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2040_;
}
else
{
goto v___jp_2022_;
}
}
else
{
goto v___jp_2022_;
}
v___jp_2022_:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1999_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v_fst_2025_ = lean_ctor_get(v_a_2024_, 0);
lean_inc_n(v_fst_2025_, 2);
v_snd_2026_ = lean_ctor_get(v_a_2024_, 1);
lean_inc(v_snd_2026_);
lean_dec(v_a_2024_);
v___x_2027_ = lean_box(0);
v___f_2028_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2028_, 0, v___x_2027_);
lean_closure_set(v___f_2028_, 1, v_snd_2026_);
lean_closure_set(v___f_2028_, 2, v_ident_2021_);
lean_closure_set(v___f_2028_, 3, v_fst_2025_);
v___x_2029_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2025_, v___f_2028_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
return v___x_2029_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_ident_2021_);
v_a_2030_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2023_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2023_);
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
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2041_ = l_Lean_Syntax_getArg(v___x_2015_, v___x_2014_);
lean_dec(v___x_2015_);
v___x_2042_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
lean_inc(v___x_2041_);
v___x_2043_ = l_Lean_Syntax_isOfKind(v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v___x_2041_);
v___x_2044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2044_;
}
else
{
lean_object* v_ident_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_ident_2045_ = l_Lean_Syntax_getArg(v___x_2041_, v___x_2014_);
lean_dec(v___x_2041_);
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27));
lean_inc(v_ident_2045_);
v___x_2047_ = l_Lean_Syntax_isOfKind(v_ident_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v_ident_2045_);
v___x_2048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1999_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v_fst_2051_ = lean_ctor_get(v_a_2050_, 0);
lean_inc_n(v_fst_2051_, 2);
v_snd_2052_ = lean_ctor_get(v_a_2050_, 1);
lean_inc(v_snd_2052_);
lean_dec(v_a_2050_);
v___x_2053_ = lean_box(0);
v___f_2054_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2054_, 0, v___x_2053_);
lean_closure_set(v___f_2054_, 1, v_snd_2052_);
lean_closure_set(v___f_2054_, 2, v_ident_2045_);
lean_closure_set(v___f_2054_, 3, v_fst_2051_);
v___x_2055_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_2051_, v___f_2054_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
return v___x_2055_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_ident_2045_);
v_a_2056_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2049_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2049_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1997_ = stack[0].m_obj;
lean_object* v_a_1998_ = stack[1].m_obj;
lean_object* v_a_1999_ = stack[2].m_obj;
lean_object* v_a_2000_ = stack[3].m_obj;
lean_object* v_a_2001_ = stack[4].m_obj;
lean_object* v_a_2002_ = stack[5].m_obj;
lean_object* v_a_2003_ = stack[6].m_obj;
lean_object* v_a_2004_ = stack[7].m_obj;
lean_object* v_a_2005_ = stack[8].m_obj;
lean_object* v_res_2064_;
v_res_2064_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(v_x_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
stack->m_obj
 = v_res_2064_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(lean_object* v_x_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(v_x_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
return v_res_2075_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(lean_object* v_mvarId_2076_, lean_object* v_val_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_mvarId_2076_, v_val_2077_, v___y_2083_);
return v___x_2087_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2076_ = stack[0].m_obj;
lean_object* v_val_2077_ = stack[1].m_obj;
lean_object* v___y_2078_ = stack[2].m_obj;
lean_object* v___y_2079_ = stack[3].m_obj;
lean_object* v___y_2080_ = stack[4].m_obj;
lean_object* v___y_2081_ = stack[5].m_obj;
lean_object* v___y_2082_ = stack[6].m_obj;
lean_object* v___y_2083_ = stack[7].m_obj;
lean_object* v___y_2084_ = stack[8].m_obj;
lean_object* v___y_2085_ = stack[9].m_obj;
lean_object* v_res_2088_;
v_res_2088_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(v_mvarId_2076_, v_val_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2088_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(lean_object* v_mvarId_2089_, lean_object* v_val_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(v_mvarId_2089_, v_val_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2100_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_object* v_00_u03b1_2101_, lean_object* v_name_2102_, lean_object* v_type_2103_, lean_object* v_val_2104_, lean_object* v_k_2105_, uint8_t v_nondep_2106_, uint8_t v_kind_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_2102_, v_type_2103_, v_val_2104_, v_k_2105_, v_nondep_2106_, v_kind_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2102_ = stack[1].m_obj;
lean_object* v_type_2103_ = stack[2].m_obj;
lean_object* v_val_2104_ = stack[3].m_obj;
lean_object* v_k_2105_ = stack[4].m_obj;
uint8_t v_nondep_2106_ = stack[5].m_num;
uint8_t v_kind_2107_ = stack[6].m_num;
lean_object* v___y_2108_ = stack[7].m_obj;
lean_object* v___y_2109_ = stack[8].m_obj;
lean_object* v___y_2110_ = stack[9].m_obj;
lean_object* v___y_2111_ = stack[10].m_obj;
lean_object* v___y_2112_ = stack[11].m_obj;
lean_object* v___y_2113_ = stack[12].m_obj;
lean_object* v___y_2114_ = stack[13].m_obj;
lean_object* v___y_2115_ = stack[14].m_obj;
lean_object* v_res_2118_;
v_res_2118_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(lean_box(0), v_name_2102_, v_type_2103_, v_val_2104_, v_k_2105_, v_nondep_2106_, v_kind_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
stack->m_obj
 = v_res_2118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_name_2120_, lean_object* v_type_2121_, lean_object* v_val_2122_, lean_object* v_k_2123_, lean_object* v_nondep_2124_, lean_object* v_kind_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v_nondep_boxed_2135_; uint8_t v_kind_boxed_2136_; lean_object* v_res_2137_; 
v_nondep_boxed_2135_ = lean_unbox(v_nondep_2124_);
v_kind_boxed_2136_ = lean_unbox(v_kind_2125_);
v_res_2137_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(v_00_u03b1_2119_, v_name_2120_, v_type_2121_, v_val_2122_, v_k_2123_, v_nondep_boxed_2135_, v_kind_boxed_2136_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2137_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2138_ = stack[0].m_obj;
lean_object* v___y_2139_ = stack[1].m_obj;
lean_object* v___y_2140_ = stack[2].m_obj;
lean_object* v___y_2141_ = stack[3].m_obj;
lean_object* v_res_2144_;
v_res_2144_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
stack->m_obj
 = v_res_2144_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2150_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_object* v_00_u03b1_2151_, lean_object* v_msg_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2152_ = stack[1].m_obj;
lean_object* v___y_2153_ = stack[2].m_obj;
lean_object* v___y_2154_ = stack[3].m_obj;
lean_object* v___y_2155_ = stack[4].m_obj;
lean_object* v___y_2156_ = stack[5].m_obj;
lean_object* v_res_2159_;
v_res_2159_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(lean_box(0), v_msg_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
stack->m_obj
 = v_res_2159_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_msg_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(v_00_u03b1_2160_, v_msg_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2167_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2168_, lean_object* v_name_2169_, uint8_t v_bi_2170_, lean_object* v_type_2171_, lean_object* v_k_2172_, uint8_t v_kind_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_2169_, v_bi_2170_, v_type_2171_, v_k_2172_, v_kind_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2169_ = stack[1].m_obj;
uint8_t v_bi_2170_ = stack[2].m_num;
lean_object* v_type_2171_ = stack[3].m_obj;
lean_object* v_k_2172_ = stack[4].m_obj;
uint8_t v_kind_2173_ = stack[5].m_num;
lean_object* v___y_2174_ = stack[6].m_obj;
lean_object* v___y_2175_ = stack[7].m_obj;
lean_object* v___y_2176_ = stack[8].m_obj;
lean_object* v___y_2177_ = stack[9].m_obj;
lean_object* v_res_2180_;
v_res_2180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(lean_box(0), v_name_2169_, v_bi_2170_, v_type_2171_, v_k_2172_, v_kind_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
stack->m_obj
 = v_res_2180_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_name_2182_, lean_object* v_bi_2183_, lean_object* v_type_2184_, lean_object* v_k_2185_, lean_object* v_kind_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v_bi_boxed_2192_; uint8_t v_kind_boxed_2193_; lean_object* v_res_2194_; 
v_bi_boxed_2192_ = lean_unbox(v_bi_2183_);
v_kind_boxed_2193_ = lean_unbox(v_kind_2186_);
v_res_2194_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(v_00_u03b1_2181_, v_name_2182_, v_bi_boxed_2192_, v_type_2184_, v_k_2185_, v_kind_boxed_2193_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2194_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_object* v_00_u03b1_2195_, lean_object* v_name_2196_, lean_object* v_type_2197_, lean_object* v_k_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_2196_, v_type_2197_, v_k_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2196_ = stack[1].m_obj;
lean_object* v_type_2197_ = stack[2].m_obj;
lean_object* v_k_2198_ = stack[3].m_obj;
lean_object* v___y_2199_ = stack[4].m_obj;
lean_object* v___y_2200_ = stack[5].m_obj;
lean_object* v___y_2201_ = stack[6].m_obj;
lean_object* v___y_2202_ = stack[7].m_obj;
lean_object* v_res_2205_;
v_res_2205_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(lean_box(0), v_name_2196_, v_type_2197_, v_k_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
stack->m_obj
 = v_res_2205_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_name_2207_, lean_object* v_type_2208_, lean_object* v_k_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(v_00_u03b1_2206_, v_name_2207_, v_type_2208_, v_k_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(lean_object* v_00_u03b2_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_x_2217_, v_x_2218_, v_x_2219_);
return v___x_2220_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2221_, lean_object* v_x_2222_, size_t v_x_2223_, size_t v_x_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_2222_, v_x_2223_, v_x_2224_, v_x_2225_, v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2222_ = stack[1].m_obj;
size_t v_x_2223_ = stack[2].m_num;
size_t v_x_2224_ = stack[3].m_num;
lean_object* v_x_2225_ = stack[4].m_obj;
lean_object* v_x_2226_ = stack[5].m_obj;
lean_object* v_res_2228_;
v_res_2228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(lean_box(0), v_x_2222_, v_x_2223_, v_x_2224_, v_x_2225_, v_x_2226_);
stack->m_obj
 = v_res_2228_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
size_t v_x_19549__boxed_2235_; size_t v_x_19550__boxed_2236_; lean_object* v_res_2237_; 
v_x_19549__boxed_2235_ = lean_unbox_usize(v_x_2231_);
lean_dec(v_x_2231_);
v_x_19550__boxed_2236_ = lean_unbox_usize(v_x_2232_);
lean_dec(v_x_2232_);
v_res_2237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(v_00_u03b2_2229_, v_x_2230_, v_x_19549__boxed_2235_, v_x_19550__boxed_2236_, v_x_2233_, v_x_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2238_, lean_object* v_n_2239_, lean_object* v_k_2240_, lean_object* v_v_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v_n_2239_, v_k_2240_, v_v_2241_);
return v___x_2242_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b2_2243_, size_t v_depth_2244_, lean_object* v_keys_2245_, lean_object* v_vals_2246_, lean_object* v_heq_2247_, lean_object* v_i_2248_, lean_object* v_entries_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_2244_, v_keys_2245_, v_vals_2246_, v_i_2248_, v_entries_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2244_ = stack[1].m_num;
lean_object* v_keys_2245_ = stack[2].m_obj;
lean_object* v_vals_2246_ = stack[3].m_obj;
lean_object* v_i_2248_ = stack[5].m_obj;
lean_object* v_entries_2249_ = stack[6].m_obj;
lean_object* v_res_2251_;
v_res_2251_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(lean_box(0), v_depth_2244_, v_keys_2245_, v_vals_2246_, lean_box(0), v_i_2248_, v_entries_2249_);
stack->m_obj
 = v_res_2251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b2_2252_, lean_object* v_depth_2253_, lean_object* v_keys_2254_, lean_object* v_vals_2255_, lean_object* v_heq_2256_, lean_object* v_i_2257_, lean_object* v_entries_2258_){
_start:
{
size_t v_depth_boxed_2259_; lean_object* v_res_2260_; 
v_depth_boxed_2259_ = lean_unbox_usize(v_depth_2253_);
lean_dec(v_depth_2253_);
v_res_2260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(v_00_u03b2_2252_, v_depth_boxed_2259_, v_keys_2254_, v_vals_2255_, v_heq_2256_, v_i_2257_, v_entries_2258_);
lean_dec_ref(v_vals_2255_);
lean_dec_ref(v_keys_2254_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_2261_, lean_object* v_x_2262_, lean_object* v_x_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_x_2262_, v_x_2263_, v_x_2264_, v_x_2265_);
return v___x_2266_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1(){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2278_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2279_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_2280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3));
v___x_2281_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed), 10, 0);
v___x_2282_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2278_, v___x_2279_, v___x_2280_, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2283_;
v_res_2283_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
stack->m_obj
 = v_res_2283_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
return v_res_2285_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
