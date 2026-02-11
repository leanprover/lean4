// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineCandidate
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM
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
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__0;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__1;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2;
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0_value;
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__0_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__1 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__1_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__2 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3;
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_override"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`inline` applied to non-local declaration '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`inline` applied to constructor '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.Simp.InlineCandidate"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Simp.inlineCandidate\?"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 120, .m_capacity = 120, .m_length = 119, .m_data = "assertion violation: ( __do_lift._@.Lean.Compiler.LCNF.Simp.InlineCandidate.450150219._hygCtx._hyg.45.0 ).isSome\n      "};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`inline` applied to parameters is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14;
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 182, 14, 42, 67, 101, 187, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 104, 221, 94, 203, 189, 176, 167)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "InlineCandidate"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 189, 245, 204, 189, 57, 91, 44)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(205, 24, 147, 136, 109, 69, 105, 125)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 141, 161, 237, 187, 152, 47, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 100, 105, 35, 144, 92, 153, 253)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 251, 144, 255, 136, 239, 26, 27)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 121, 5, 69, 12, 122, 72, 166)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 124, 205, 76, 48, 189, 94, 107)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 5, 164, 203, 90, 240, 32, 95)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 174, 208, 245, 188, 159, 42, 16)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 214, 115, 185, 35, 209, 42, 75)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 210, 134, 178, 101, 107, 79, 160)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 132, 0, 16, 135, 249, 121, 4)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 86, 216, 181, 78, 83, 157, 191)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1449551352) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 111, 212, 97, 188, 2, 254, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 181, 10, 223, 32, 170, 74, 213)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 22, 140, 58, 145, 25, 234, 208)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(98, 140, 124, 200, 122, 12, 67, 204)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_isInstanceReducibleCore(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg(x_1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5);
x_10 = lean_st_ref_get(x_3);
x_11 = l_Lean_Compiler_LCNF_getPurity___redArg(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = lean_unbox(x_13);
lean_dec(x_13);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16, x_18);
lean_dec_ref(x_16);
x_20 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2;
lean_inc_ref(x_7);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_7);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 0, x_21);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_unbox(x_13);
lean_dec(x_13);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23, x_24);
lean_dec_ref(x_23);
x_26 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2;
lean_inc_ref(x_7);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_7);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = lean_unbox(x_30);
lean_dec(x_30);
x_35 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_32, x_34);
lean_dec_ref(x_32);
x_36 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2;
lean_inc_ref(x_7);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_7);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(3, 2, 0);
} else {
 x_38 = x_33;
 lean_ctor_set_tag(x_38, 3);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
lean_inc(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0;
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1));
x_22 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2));
lean_inc_ref(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_13, 4, x_26);
lean_ctor_set(x_13, 3, x_27);
lean_ctor_set(x_13, 2, x_28);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_22);
x_29 = l_ReaderT_instMonad___redArg(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_40 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = lean_box(0);
x_50 = l_instInhabitedOfMonad___redArg(x_48, x_49);
x_51 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_panic_fn(x_51, x_1);
x_53 = lean_apply_8(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 2);
x_56 = lean_ctor_get(x_31, 3);
x_57 = lean_ctor_get(x_31, 4);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_58 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_59 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_54);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_54);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_57);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_56);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_55);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_64);
lean_ctor_set(x_66, 4, x_63);
lean_ctor_set(x_29, 1, x_59);
lean_ctor_set(x_29, 0, x_66);
x_67 = l_ReaderT_instMonad___redArg(x_29);
x_68 = l_ReaderT_instMonad___redArg(x_67);
x_69 = lean_box(0);
x_70 = l_instInhabitedOfMonad___redArg(x_68, x_69);
x_71 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = lean_panic_fn(x_71, x_1);
x_73 = lean_apply_8(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_74 = lean_ctor_get(x_29, 0);
lean_inc(x_74);
lean_dec(x_29);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_74, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 4);
lean_inc(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
x_80 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_81 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_75);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_83, 0, x_75);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_85, 0, x_78);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_86, 0, x_77);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_87, 0, x_76);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_86);
lean_ctor_set(x_88, 4, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
x_90 = l_ReaderT_instMonad___redArg(x_89);
x_91 = l_ReaderT_instMonad___redArg(x_90);
x_92 = lean_box(0);
x_93 = l_instInhabitedOfMonad___redArg(x_91, x_92);
x_94 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_94, 0, x_93);
x_95 = lean_panic_fn(x_94, x_1);
x_96 = lean_apply_8(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_97 = lean_ctor_get(x_13, 0);
x_98 = lean_ctor_get(x_13, 2);
x_99 = lean_ctor_get(x_13, 3);
x_100 = lean_ctor_get(x_13, 4);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_13);
x_101 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1));
x_102 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2));
lean_inc_ref(x_97);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_103, 0, x_97);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_104, 0, x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_106, 0, x_100);
x_107 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_107, 0, x_99);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_108, 0, x_98);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set(x_109, 4, x_106);
lean_ctor_set(x_11, 1, x_102);
lean_ctor_set(x_11, 0, x_109);
x_110 = l_ReaderT_instMonad___redArg(x_11);
x_111 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_111, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 4);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
x_118 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_119 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_113);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_120, 0, x_113);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_121, 0, x_113);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_123, 0, x_116);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_124, 0, x_115);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_125, 0, x_114);
if (lean_is_scalar(x_117)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_117;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_118);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_124);
lean_ctor_set(x_126, 4, x_123);
if (lean_is_scalar(x_112)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_112;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_119);
x_128 = l_ReaderT_instMonad___redArg(x_127);
x_129 = l_ReaderT_instMonad___redArg(x_128);
x_130 = lean_box(0);
x_131 = l_instInhabitedOfMonad___redArg(x_129, x_130);
x_132 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_132, 0, x_131);
x_133 = lean_panic_fn(x_132, x_1);
x_134 = lean_apply_8(x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_135 = lean_ctor_get(x_11, 0);
lean_inc(x_135);
lean_dec(x_11);
x_136 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_135, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 4);
lean_inc(x_139);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 x_140 = x_135;
} else {
 lean_dec_ref(x_135);
 x_140 = lean_box(0);
}
x_141 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1));
x_142 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2));
lean_inc_ref(x_136);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_143, 0, x_136);
x_144 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_144, 0, x_136);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_146, 0, x_139);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_147, 0, x_138);
x_148 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_148, 0, x_137);
if (lean_is_scalar(x_140)) {
 x_149 = lean_alloc_ctor(0, 5, 0);
} else {
 x_149 = x_140;
}
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_141);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_147);
lean_ctor_set(x_149, 4, x_146);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_142);
x_151 = l_ReaderT_instMonad___redArg(x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_152, 0);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_152, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_152, 4);
lean_inc(x_157);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 x_158 = x_152;
} else {
 lean_dec_ref(x_152);
 x_158 = lean_box(0);
}
x_159 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_160 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_154);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_161, 0, x_154);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_162, 0, x_154);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_164, 0, x_157);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_165, 0, x_156);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_166, 0, x_155);
if (lean_is_scalar(x_158)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_158;
}
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_159);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set(x_167, 4, x_164);
if (lean_is_scalar(x_153)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_153;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_160);
x_169 = l_ReaderT_instMonad___redArg(x_168);
x_170 = l_ReaderT_instMonad___redArg(x_169);
x_171 = lean_box(0);
x_172 = l_instInhabitedOfMonad___redArg(x_170, x_171);
x_173 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_173, 0, x_172);
x_174 = lean_panic_fn(x_173, x_1);
x_175 = lean_apply_8(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_175;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; uint8_t x_22; 
x_22 = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(x_1);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(x_1);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_1);
x_14 = x_24;
goto block_21;
}
else
{
x_14 = x_23;
goto block_21;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_4);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
block_21:
{
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(x_2, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(x_3);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(x_4);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0;
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1));
x_22 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2));
lean_inc_ref(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_13, 4, x_26);
lean_ctor_set(x_13, 3, x_27);
lean_ctor_set(x_13, 2, x_28);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_22);
x_29 = l_ReaderT_instMonad___redArg(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_40 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 2);
x_55 = lean_ctor_get(x_50, 3);
x_56 = lean_ctor_get(x_50, 4);
x_57 = lean_ctor_get(x_50, 1);
lean_dec(x_57);
x_58 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_59 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_53);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_53);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_56);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_55);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_54);
lean_ctor_set(x_50, 4, x_63);
lean_ctor_set(x_50, 3, x_64);
lean_ctor_set(x_50, 2, x_65);
lean_ctor_set(x_50, 1, x_58);
lean_ctor_set(x_50, 0, x_62);
lean_ctor_set(x_48, 1, x_59);
x_66 = lean_box(0);
x_67 = l_instInhabitedOfMonad___redArg(x_48, x_66);
x_68 = lean_panic_fn(x_67, x_1);
x_69 = lean_apply_8(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_70 = lean_ctor_get(x_50, 0);
x_71 = lean_ctor_get(x_50, 2);
x_72 = lean_ctor_get(x_50, 3);
x_73 = lean_ctor_get(x_50, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_50);
x_74 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_75 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_70);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_70);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_73);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_71);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_48, 1, x_75);
lean_ctor_set(x_48, 0, x_82);
x_83 = lean_box(0);
x_84 = l_instInhabitedOfMonad___redArg(x_48, x_83);
x_85 = lean_panic_fn(x_84, x_1);
x_86 = lean_apply_8(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_87 = lean_ctor_get(x_48, 0);
lean_inc(x_87);
lean_dec(x_48);
x_88 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_87, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 4);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_94 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_88);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_88);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_91);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_90);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_89);
if (lean_is_scalar(x_92)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_92;
}
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_94);
x_103 = lean_box(0);
x_104 = l_instInhabitedOfMonad___redArg(x_102, x_103);
x_105 = lean_panic_fn(x_104, x_1);
x_106 = lean_apply_8(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_107 = lean_ctor_get(x_31, 0);
x_108 = lean_ctor_get(x_31, 2);
x_109 = lean_ctor_get(x_31, 3);
x_110 = lean_ctor_get(x_31, 4);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_31);
x_111 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_112 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_107);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_113, 0, x_107);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_116, 0, x_110);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_118, 0, x_108);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_117);
lean_ctor_set(x_119, 4, x_116);
lean_ctor_set(x_29, 1, x_112);
lean_ctor_set(x_29, 0, x_119);
x_120 = l_ReaderT_instMonad___redArg(x_29);
x_121 = l_ReaderT_instMonad___redArg(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_122, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_122, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 4);
lean_inc(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
x_129 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_130 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_124);
x_131 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_131, 0, x_124);
x_132 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_132, 0, x_124);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_127);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_135, 0, x_126);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_136, 0, x_125);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_135);
lean_ctor_set(x_137, 4, x_134);
if (lean_is_scalar(x_123)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_123;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
x_139 = lean_box(0);
x_140 = l_instInhabitedOfMonad___redArg(x_138, x_139);
x_141 = lean_panic_fn(x_140, x_1);
x_142 = lean_apply_8(x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_143 = lean_ctor_get(x_29, 0);
lean_inc(x_143);
lean_dec(x_29);
x_144 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_143, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
x_149 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_150 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = l_ReaderT_instMonad___redArg(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_161, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 4);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
x_168 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_169 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_163);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_170, 0, x_163);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_171, 0, x_163);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_173, 0, x_166);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_174, 0, x_165);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_175, 0, x_164);
if (lean_is_scalar(x_167)) {
 x_176 = lean_alloc_ctor(0, 5, 0);
} else {
 x_176 = x_167;
}
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_168);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_174);
lean_ctor_set(x_176, 4, x_173);
if (lean_is_scalar(x_162)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_162;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_169);
x_178 = lean_box(0);
x_179 = l_instInhabitedOfMonad___redArg(x_177, x_178);
x_180 = lean_panic_fn(x_179, x_1);
x_181 = lean_apply_8(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_182 = lean_ctor_get(x_13, 0);
x_183 = lean_ctor_get(x_13, 2);
x_184 = lean_ctor_get(x_13, 3);
x_185 = lean_ctor_get(x_13, 4);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_13);
x_186 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1));
x_187 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2));
lean_inc_ref(x_182);
x_188 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_188, 0, x_182);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_189, 0, x_182);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_191, 0, x_185);
x_192 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_192, 0, x_184);
x_193 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_193, 0, x_183);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_186);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_192);
lean_ctor_set(x_194, 4, x_191);
lean_ctor_set(x_11, 1, x_187);
lean_ctor_set(x_11, 0, x_194);
x_195 = l_ReaderT_instMonad___redArg(x_11);
x_196 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_196, 0);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
x_203 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_204 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_198);
x_205 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_205, 0, x_198);
x_206 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_206, 0, x_198);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_208, 0, x_201);
x_209 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_209, 0, x_200);
x_210 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_210, 0, x_199);
if (lean_is_scalar(x_202)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_202;
}
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_203);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_211, 3, x_209);
lean_ctor_set(x_211, 4, x_208);
if (lean_is_scalar(x_197)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_197;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_204);
x_213 = l_ReaderT_instMonad___redArg(x_212);
x_214 = l_ReaderT_instMonad___redArg(x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc_ref(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_215, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_215, 4);
lean_inc(x_220);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 lean_ctor_release(x_215, 4);
 x_221 = x_215;
} else {
 lean_dec_ref(x_215);
 x_221 = lean_box(0);
}
x_222 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_223 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_217);
x_224 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_224, 0, x_217);
x_225 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_225, 0, x_217);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_227, 0, x_220);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_228, 0, x_219);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_229, 0, x_218);
if (lean_is_scalar(x_221)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_221;
}
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_222);
lean_ctor_set(x_230, 2, x_229);
lean_ctor_set(x_230, 3, x_228);
lean_ctor_set(x_230, 4, x_227);
if (lean_is_scalar(x_216)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_216;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_223);
x_232 = lean_box(0);
x_233 = l_instInhabitedOfMonad___redArg(x_231, x_232);
x_234 = lean_panic_fn(x_233, x_1);
x_235 = lean_apply_8(x_234, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_236 = lean_ctor_get(x_11, 0);
lean_inc(x_236);
lean_dec(x_11);
x_237 = lean_ctor_get(x_236, 0);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_236, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 4);
lean_inc(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
x_242 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__1));
x_243 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__2));
lean_inc_ref(x_237);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_244, 0, x_237);
x_245 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_245, 0, x_237);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_247, 0, x_240);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_248, 0, x_239);
x_249 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_249, 0, x_238);
if (lean_is_scalar(x_241)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_241;
}
lean_ctor_set(x_250, 0, x_246);
lean_ctor_set(x_250, 1, x_242);
lean_ctor_set(x_250, 2, x_249);
lean_ctor_set(x_250, 3, x_248);
lean_ctor_set(x_250, 4, x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_243);
x_252 = l_ReaderT_instMonad___redArg(x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc_ref(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_253, 0);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_253, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 4);
lean_inc(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
 x_259 = lean_box(0);
}
x_260 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__3));
x_261 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__4));
lean_inc_ref(x_255);
x_262 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_262, 0, x_255);
x_263 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_263, 0, x_255);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_265, 0, x_258);
x_266 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_266, 0, x_257);
x_267 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_267, 0, x_256);
if (lean_is_scalar(x_259)) {
 x_268 = lean_alloc_ctor(0, 5, 0);
} else {
 x_268 = x_259;
}
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_260);
lean_ctor_set(x_268, 2, x_267);
lean_ctor_set(x_268, 3, x_266);
lean_ctor_set(x_268, 4, x_265);
if (lean_is_scalar(x_254)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_254;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_261);
x_270 = l_ReaderT_instMonad___redArg(x_269);
x_271 = l_ReaderT_instMonad___redArg(x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc_ref(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_272, 0);
lean_inc_ref(x_274);
x_275 = lean_ctor_get(x_272, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 4);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__0));
x_280 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___closed__1));
lean_inc_ref(x_274);
x_281 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_281, 0, x_274);
x_282 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_282, 0, x_274);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_284, 0, x_277);
x_285 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_285, 0, x_276);
x_286 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_286, 0, x_275);
if (lean_is_scalar(x_278)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_278;
}
lean_ctor_set(x_287, 0, x_283);
lean_ctor_set(x_287, 1, x_279);
lean_ctor_set(x_287, 2, x_286);
lean_ctor_set(x_287, 3, x_285);
lean_ctor_set(x_287, 4, x_284);
if (lean_is_scalar(x_273)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_273;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_280);
x_289 = lean_box(0);
x_290 = l_instInhabitedOfMonad___redArg(x_288, x_289);
x_291 = lean_panic_fn(x_290, x_1);
x_292 = lean_apply_8(x_291, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_292;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(121u);
x_4 = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__1));
x_5 = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8);
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
lean_dec(x_10);
x_15 = 0;
x_16 = l_Lean_Environment_findAsync_x3f(x_14, x_1, x_15);
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
if (x_19 == 6)
{
lean_object* x_20; 
x_20 = l_Lean_AsyncConstantInfo_toConstantInfo(x_18);
if (lean_obj_tag(x_20) == 6)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_16, 0, x_22);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_16);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_20);
lean_free_object(x_16);
x_25 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3;
x_26 = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
else
{
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*3);
if (x_28 == 6)
{
lean_object* x_29; 
x_29 = l_Lean_AsyncConstantInfo_toConstantInfo(x_27);
if (lean_obj_tag(x_29) == 6)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_31;
 lean_ctor_set_tag(x_33, 0);
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_29);
x_34 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3;
x_35 = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_spec__1(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_35;
}
}
else
{
lean_dec(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(54u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_18 = 0;
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_1, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 1)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_379, 0);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_381 = lean_ctor_get(x_1, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_382);
lean_dec_ref(x_1);
x_383 = lean_ctor_get(x_379, 1);
x_384 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1));
x_385 = lean_string_dec_eq(x_383, x_384);
if (x_385 == 0)
{
x_186 = x_379;
x_187 = x_381;
x_188 = x_382;
x_189 = x_18;
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = lean_box(0);
goto block_241;
}
else
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_386 = lean_array_get_size(x_382);
x_387 = lean_unsigned_to_nat(2u);
x_388 = lean_nat_dec_eq(x_386, x_387);
if (x_388 == 0)
{
x_186 = x_379;
x_187 = x_381;
x_188 = x_382;
x_189 = x_18;
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = lean_box(0);
goto block_241;
}
else
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_unsigned_to_nat(1u);
x_390 = lean_array_fget_borrowed(x_382, x_389);
if (lean_obj_tag(x_390) == 1)
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; 
lean_inc_ref(x_390);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec_ref(x_379);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = 0;
lean_inc(x_391);
x_393 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(x_392, x_391, x_6);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
lean_dec_ref(x_393);
if (lean_obj_tag(x_394) == 1)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_391);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
x_397 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2;
x_327 = x_396;
x_328 = x_397;
x_329 = x_388;
x_330 = x_3;
x_331 = x_5;
x_332 = x_6;
x_333 = x_7;
x_334 = x_8;
x_335 = lean_box(0);
goto block_360;
}
else
{
lean_object* x_398; 
lean_dec(x_394);
x_398 = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(x_392, x_391, x_6);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
if (lean_obj_tag(x_399) == 1)
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_391);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
x_401 = lean_ctor_get(x_400, 3);
lean_inc(x_401);
lean_dec(x_400);
if (lean_obj_tag(x_401) == 3)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_401, 2);
lean_inc_ref(x_404);
lean_dec_ref(x_401);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_402);
x_405 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec_ref(x_405);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; 
x_407 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; uint8_t x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec_ref(x_407);
x_409 = lean_unbox(x_408);
lean_dec(x_408);
x_410 = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(x_402, x_409, x_8);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
if (lean_obj_tag(x_411) == 1)
{
lean_dec_ref(x_411);
x_186 = x_402;
x_187 = x_403;
x_188 = x_404;
x_189 = x_388;
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = lean_box(0);
goto block_241;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_411);
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_412 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4;
x_413 = l_Lean_MessageData_ofName(x_402);
x_414 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
x_415 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6;
x_416 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_416, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
return x_417;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
}
}
else
{
uint8_t x_421; 
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_421 = !lean_is_exclusive(x_410);
if (x_421 == 0)
{
return x_410;
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_410, 0);
lean_inc(x_422);
lean_dec(x_410);
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_422);
return x_423;
}
}
}
else
{
uint8_t x_424; 
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_424 = !lean_is_exclusive(x_407);
if (x_424 == 0)
{
return x_407;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_407, 0);
lean_inc(x_425);
lean_dec(x_407);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
return x_426;
}
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
lean_dec_ref(x_406);
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_427 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8;
x_428 = l_Lean_MessageData_ofName(x_402);
x_429 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6;
x_431 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
x_432 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_431, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_433 = !lean_is_exclusive(x_432);
if (x_433 == 0)
{
return x_432;
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
}
else
{
uint8_t x_436; 
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_436 = !lean_is_exclusive(x_405);
if (x_436 == 0)
{
return x_405;
}
else
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_405, 0);
lean_inc(x_437);
lean_dec(x_405);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
}
}
else
{
x_361 = x_401;
x_362 = x_388;
x_363 = x_2;
x_364 = x_3;
x_365 = x_4;
x_366 = x_5;
x_367 = x_6;
x_368 = x_7;
x_369 = x_8;
x_370 = lean_box(0);
goto block_378;
}
}
else
{
lean_object* x_439; 
lean_dec(x_399);
x_439 = l_Lean_Compiler_LCNF_findParam_x3f___redArg(x_392, x_391, x_6);
lean_dec(x_391);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12;
x_442 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3(x_441, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; 
lean_dec_ref(x_440);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_443 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14;
x_444 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_443, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
return x_444;
}
else
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_446);
return x_447;
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_448 = !lean_is_exclusive(x_439);
if (x_448 == 0)
{
return x_439;
}
else
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_439, 0);
lean_inc(x_449);
lean_dec(x_439);
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
}
}
}
else
{
uint8_t x_451; 
lean_dec(x_391);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_451 = !lean_is_exclusive(x_398);
if (x_451 == 0)
{
return x_398;
}
else
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_398, 0);
lean_inc(x_452);
lean_dec(x_398);
x_453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_453, 0, x_452);
return x_453;
}
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_391);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_454 = !lean_is_exclusive(x_393);
if (x_454 == 0)
{
return x_393;
}
else
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_393, 0);
lean_inc(x_455);
lean_dec(x_393);
x_456 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_456, 0, x_455);
return x_456;
}
}
}
else
{
x_186 = x_379;
x_187 = x_381;
x_188 = x_382;
x_189 = x_18;
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = lean_box(0);
goto block_241;
}
}
}
}
else
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_1, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_458);
lean_dec_ref(x_1);
x_186 = x_379;
x_187 = x_457;
x_188 = x_458;
x_189 = x_18;
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = lean_box(0);
goto block_241;
}
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_ctor_get(x_1, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_460);
lean_dec_ref(x_1);
x_186 = x_379;
x_187 = x_459;
x_188 = x_460;
x_189 = x_18;
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = lean_box(0);
goto block_241;
}
}
else
{
x_361 = x_1;
x_362 = x_18;
x_363 = x_2;
x_364 = x_3;
x_365 = x_4;
x_366 = x_5;
x_367 = x_6;
x_368 = x_7;
x_369 = x_8;
x_370 = lean_box(0);
goto block_378;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_48:
{
lean_object* x_29; 
x_29 = l_Lean_Compiler_LCNF_Simp_incInline___redArg(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec_ref(x_23);
lean_inc(x_19);
lean_inc_ref(x_21);
x_33 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_20, x_21, x_19);
lean_inc(x_19);
x_34 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(x_24, x_32, x_19);
x_35 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(x_21, x_19);
x_36 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_36, sizeof(void*)*4 + 1, x_22);
lean_ctor_set_uint8(x_36, sizeof(void*)*4 + 2, x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_29);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec_ref(x_23);
lean_inc(x_19);
lean_inc_ref(x_21);
x_39 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_20, x_21, x_19);
lean_inc(x_19);
x_40 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(x_24, x_38, x_19);
x_41 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(x_21, x_19);
x_42 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_25);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 1, x_22);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 2, x_26);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_19);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
block_99:
{
if (x_53 == 0)
{
lean_dec(x_59);
lean_dec(x_56);
x_19 = x_49;
x_20 = x_50;
x_21 = x_52;
x_22 = x_53;
x_23 = x_54;
x_24 = x_55;
x_25 = x_57;
x_26 = x_58;
x_27 = x_60;
x_28 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_61; 
lean_inc_ref(x_52);
x_61 = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(x_52);
if (lean_obj_tag(x_61) == 1)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_array_get_size(x_57);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_66 = lean_box(0);
lean_ctor_set_tag(x_61, 0);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_61);
x_67 = lean_box(0);
x_68 = lean_array_get_borrowed(x_67, x_57, x_63);
lean_dec(x_63);
x_69 = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(x_68, x_59, x_56);
lean_dec(x_56);
lean_dec(x_59);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_60);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_73 = lean_box(0);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_free_object(x_69);
x_19 = x_49;
x_20 = x_50;
x_21 = x_52;
x_22 = x_53;
x_23 = x_54;
x_24 = x_55;
x_25 = x_57;
x_26 = x_58;
x_27 = x_60;
x_28 = lean_box(0);
goto block_48;
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_60);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
else
{
x_19 = x_49;
x_20 = x_50;
x_21 = x_52;
x_22 = x_53;
x_23 = x_54;
x_24 = x_55;
x_25 = x_57;
x_26 = x_58;
x_27 = x_60;
x_28 = lean_box(0);
goto block_48;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_60);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
return x_69;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
lean_dec(x_61);
x_82 = lean_array_get_size(x_57);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_box(0);
x_87 = lean_array_get_borrowed(x_86, x_57, x_81);
lean_dec(x_81);
x_88 = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(x_87, x_59, x_56);
lean_dec(x_56);
lean_dec(x_59);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_unbox(x_89);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_60);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_92 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
lean_dec(x_90);
x_19 = x_49;
x_20 = x_50;
x_21 = x_52;
x_22 = x_53;
x_23 = x_54;
x_24 = x_55;
x_25 = x_57;
x_26 = x_58;
x_27 = x_60;
x_28 = lean_box(0);
goto block_48;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_60);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec(x_49);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
block_131:
{
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_free_object(x_113);
lean_dec(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_106);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec(x_100);
x_10 = lean_box(0);
goto block_13;
}
else
{
if (x_105 == 0)
{
if (x_108 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_106);
x_118 = lean_array_get_size(x_103);
x_119 = lean_nat_dec_lt(x_118, x_117);
lean_dec(x_117);
if (x_119 == 0)
{
lean_free_object(x_113);
x_49 = x_100;
x_50 = x_101;
x_51 = lean_box(0);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_110;
x_56 = x_102;
x_57 = x_103;
x_58 = x_111;
x_59 = x_104;
x_60 = x_112;
goto block_99;
}
else
{
lean_object* x_120; 
lean_dec(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_106);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec(x_100);
x_120 = lean_box(0);
lean_ctor_set(x_113, 0, x_120);
return x_113;
}
}
else
{
lean_free_object(x_113);
x_49 = x_100;
x_50 = x_101;
x_51 = lean_box(0);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_110;
x_56 = x_102;
x_57 = x_103;
x_58 = x_111;
x_59 = x_104;
x_60 = x_112;
goto block_99;
}
}
else
{
lean_free_object(x_113);
x_49 = x_100;
x_50 = x_101;
x_51 = lean_box(0);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_110;
x_56 = x_102;
x_57 = x_103;
x_58 = x_111;
x_59 = x_104;
x_60 = x_112;
goto block_99;
}
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
lean_dec(x_113);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_dec(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_106);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec(x_100);
x_10 = lean_box(0);
goto block_13;
}
else
{
if (x_105 == 0)
{
if (x_108 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_106);
x_124 = lean_array_get_size(x_103);
x_125 = lean_nat_dec_lt(x_124, x_123);
lean_dec(x_123);
if (x_125 == 0)
{
x_49 = x_100;
x_50 = x_101;
x_51 = lean_box(0);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_110;
x_56 = x_102;
x_57 = x_103;
x_58 = x_111;
x_59 = x_104;
x_60 = x_112;
goto block_99;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_106);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec(x_100);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
x_49 = x_100;
x_50 = x_101;
x_51 = lean_box(0);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_110;
x_56 = x_102;
x_57 = x_103;
x_58 = x_111;
x_59 = x_104;
x_60 = x_112;
goto block_99;
}
}
else
{
x_49 = x_100;
x_50 = x_101;
x_51 = lean_box(0);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_110;
x_56 = x_102;
x_57 = x_103;
x_58 = x_111;
x_59 = x_104;
x_60 = x_112;
goto block_99;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_106);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec(x_100);
x_128 = !lean_is_exclusive(x_113);
if (x_128 == 0)
{
return x_113;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_113, 0);
lean_inc(x_129);
lean_dec(x_113);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
block_153:
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_box(0);
lean_inc(x_137);
lean_inc(x_139);
lean_inc(x_150);
x_152 = lean_apply_9(x_136, x_151, x_149, x_150, x_143, x_133, x_139, x_140, x_137, lean_box(0));
x_100 = x_132;
x_101 = x_134;
x_102 = x_137;
x_103 = x_138;
x_104 = x_139;
x_105 = x_141;
x_106 = x_142;
x_107 = x_145;
x_108 = x_144;
x_109 = x_146;
x_110 = x_147;
x_111 = x_148;
x_112 = x_150;
x_113 = x_152;
goto block_131;
}
block_185:
{
if (x_162 == 0)
{
lean_object* x_173; 
x_173 = l_Lean_Compiler_LCNF_inBasePhase___redArg(x_155);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_box(0);
lean_inc(x_158);
lean_inc(x_161);
lean_inc(x_172);
x_177 = lean_apply_9(x_157, x_176, x_169, x_172, x_163, x_155, x_161, x_160, x_158, lean_box(0));
x_100 = x_154;
x_101 = x_156;
x_102 = x_158;
x_103 = x_159;
x_104 = x_161;
x_105 = x_162;
x_106 = x_164;
x_107 = x_165;
x_108 = x_166;
x_109 = x_167;
x_110 = x_168;
x_111 = x_171;
x_112 = x_172;
x_113 = x_177;
goto block_131;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_167, 0);
lean_inc(x_178);
x_179 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg(x_178, x_158);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = lean_unbox(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
if (lean_obj_tag(x_178) == 1)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_178, 1);
x_183 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0));
x_184 = lean_string_dec_eq(x_182, x_183);
if (x_184 == 0)
{
x_132 = x_154;
x_133 = x_155;
x_134 = x_156;
x_135 = lean_box(0);
x_136 = x_157;
x_137 = x_158;
x_138 = x_159;
x_139 = x_161;
x_140 = x_160;
x_141 = x_162;
x_142 = x_164;
x_143 = x_163;
x_144 = x_166;
x_145 = x_165;
x_146 = x_167;
x_147 = x_168;
x_148 = x_171;
x_149 = x_169;
x_150 = x_172;
goto block_153;
}
else
{
lean_dec(x_172);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
x_132 = x_154;
x_133 = x_155;
x_134 = x_156;
x_135 = lean_box(0);
x_136 = x_157;
x_137 = x_158;
x_138 = x_159;
x_139 = x_161;
x_140 = x_160;
x_141 = x_162;
x_142 = x_164;
x_143 = x_163;
x_144 = x_166;
x_145 = x_165;
x_146 = x_167;
x_147 = x_168;
x_148 = x_171;
x_149 = x_169;
x_150 = x_172;
goto block_153;
}
}
else
{
lean_dec(x_172);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_dec_ref(x_169);
lean_dec_ref(x_163);
lean_dec_ref(x_160);
lean_dec_ref(x_157);
lean_dec_ref(x_155);
x_100 = x_154;
x_101 = x_156;
x_102 = x_158;
x_103 = x_159;
x_104 = x_161;
x_105 = x_162;
x_106 = x_164;
x_107 = x_165;
x_108 = x_166;
x_109 = x_167;
x_110 = x_168;
x_111 = x_171;
x_112 = x_172;
x_113 = x_173;
goto block_131;
}
}
else
{
lean_dec_ref(x_169);
lean_dec_ref(x_163);
lean_dec_ref(x_160);
lean_dec_ref(x_157);
lean_dec_ref(x_155);
x_49 = x_154;
x_50 = x_156;
x_51 = lean_box(0);
x_52 = x_164;
x_53 = x_165;
x_54 = x_167;
x_55 = x_168;
x_56 = x_158;
x_57 = x_159;
x_58 = x_171;
x_59 = x_161;
x_60 = x_172;
goto block_99;
}
}
block_241:
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_190, 1);
x_199 = lean_ctor_get_uint8(x_198, 3);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
uint8_t x_202; lean_object* x_203; 
x_202 = lean_ctor_get_uint8(x_198, 1);
x_203 = l_Lean_Compiler_LCNF_getPhase___redArg(x_193);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_unbox(x_204);
x_206 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_186, x_205, x_195, x_196);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 0);
if (lean_obj_tag(x_208) == 1)
{
lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = lean_unbox(x_204);
lean_dec(x_204);
x_211 = l_Lean_Compiler_LCNF_Phase_toPurity(x_210);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_209, 1);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
lean_free_object(x_206);
x_213 = lean_ctor_get(x_209, 0);
lean_inc_ref(x_213);
x_214 = lean_ctor_get_uint8(x_209, sizeof(void*)*3);
x_215 = lean_ctor_get(x_212, 0);
lean_inc_ref(x_215);
x_216 = lean_box(x_18);
x_217 = lean_box(x_199);
lean_inc_ref(x_215);
lean_inc(x_209);
x_218 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed), 13, 4);
lean_closure_set(x_218, 0, x_209);
lean_closure_set(x_218, 1, x_215);
lean_closure_set(x_218, 2, x_216);
lean_closure_set(x_218, 3, x_217);
x_219 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_209);
if (x_219 == 0)
{
if (x_214 == 0)
{
x_154 = x_187;
x_155 = x_193;
x_156 = x_211;
x_157 = x_218;
x_158 = x_196;
x_159 = x_188;
x_160 = x_195;
x_161 = x_194;
x_162 = x_189;
x_163 = x_192;
x_164 = x_209;
x_165 = x_219;
x_166 = x_202;
x_167 = x_213;
x_168 = x_215;
x_169 = x_190;
x_170 = lean_box(0);
x_171 = x_214;
x_172 = x_191;
goto block_185;
}
else
{
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_213);
lean_dec(x_209);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
x_154 = x_187;
x_155 = x_193;
x_156 = x_211;
x_157 = x_218;
x_158 = x_196;
x_159 = x_188;
x_160 = x_195;
x_161 = x_194;
x_162 = x_189;
x_163 = x_192;
x_164 = x_209;
x_165 = x_219;
x_166 = x_202;
x_167 = x_213;
x_168 = x_215;
x_169 = x_190;
x_170 = lean_box(0);
x_171 = x_214;
x_172 = x_191;
goto block_185;
}
}
else
{
lean_object* x_220; 
lean_dec(x_209);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_220 = lean_box(0);
lean_ctor_set(x_206, 0, x_220);
return x_206;
}
}
else
{
lean_dec(x_209);
lean_free_object(x_206);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_free_object(x_206);
lean_dec(x_208);
lean_dec(x_204);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_206, 0);
lean_inc(x_221);
lean_dec(x_206);
if (lean_obj_tag(x_221) == 1)
{
lean_object* x_222; uint8_t x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = lean_unbox(x_204);
lean_dec(x_204);
x_224 = l_Lean_Compiler_LCNF_Phase_toPurity(x_223);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_222, 1);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_226 = lean_ctor_get(x_222, 0);
lean_inc_ref(x_226);
x_227 = lean_ctor_get_uint8(x_222, sizeof(void*)*3);
x_228 = lean_ctor_get(x_225, 0);
lean_inc_ref(x_228);
x_229 = lean_box(x_18);
x_230 = lean_box(x_199);
lean_inc_ref(x_228);
lean_inc(x_222);
x_231 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed), 13, 4);
lean_closure_set(x_231, 0, x_222);
lean_closure_set(x_231, 1, x_228);
lean_closure_set(x_231, 2, x_229);
lean_closure_set(x_231, 3, x_230);
x_232 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_222);
if (x_232 == 0)
{
if (x_227 == 0)
{
x_154 = x_187;
x_155 = x_193;
x_156 = x_224;
x_157 = x_231;
x_158 = x_196;
x_159 = x_188;
x_160 = x_195;
x_161 = x_194;
x_162 = x_189;
x_163 = x_192;
x_164 = x_222;
x_165 = x_232;
x_166 = x_202;
x_167 = x_226;
x_168 = x_228;
x_169 = x_190;
x_170 = lean_box(0);
x_171 = x_227;
x_172 = x_191;
goto block_185;
}
else
{
lean_dec_ref(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_226);
lean_dec(x_222);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
x_154 = x_187;
x_155 = x_193;
x_156 = x_224;
x_157 = x_231;
x_158 = x_196;
x_159 = x_188;
x_160 = x_195;
x_161 = x_194;
x_162 = x_189;
x_163 = x_192;
x_164 = x_222;
x_165 = x_232;
x_166 = x_202;
x_167 = x_226;
x_168 = x_228;
x_169 = x_190;
x_170 = lean_box(0);
x_171 = x_227;
x_172 = x_191;
goto block_185;
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_222);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_233);
return x_234;
}
}
else
{
lean_dec(x_222);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_dec(x_221);
lean_dec(x_204);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_204);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_235 = !lean_is_exclusive(x_206);
if (x_235 == 0)
{
return x_206;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_206, 0);
lean_inc(x_236);
lean_dec(x_206);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
x_238 = !lean_is_exclusive(x_203);
if (x_238 == 0)
{
return x_203;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_203, 0);
lean_inc(x_239);
lean_dec(x_203);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
}
}
}
block_301:
{
lean_object* x_252; 
x_252 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(x_246);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; uint8_t x_254; 
lean_dec_ref(x_252);
x_253 = lean_st_ref_take(x_246);
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_253, 6);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_255, x_256);
lean_dec(x_255);
lean_ctor_set(x_253, 6, x_257);
x_258 = lean_st_ref_set(x_246, x_253);
lean_dec(x_246);
x_259 = l_Lean_Compiler_LCNF_getType(x_245, x_243, x_248, x_249, x_250);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_243);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_ctor_get(x_242, 2);
lean_inc_ref(x_262);
x_263 = lean_ctor_get(x_242, 4);
lean_inc_ref(x_263);
lean_dec_ref(x_242);
x_264 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_261);
lean_ctor_set(x_264, 3, x_247);
lean_ctor_set_uint8(x_264, sizeof(void*)*4, x_251);
lean_ctor_set_uint8(x_264, sizeof(void*)*4 + 1, x_18);
lean_ctor_set_uint8(x_264, sizeof(void*)*4 + 2, x_18);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_259, 0, x_265);
return x_259;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_259, 0);
lean_inc(x_266);
lean_dec(x_259);
x_267 = lean_ctor_get(x_242, 2);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_242, 4);
lean_inc_ref(x_268);
lean_dec_ref(x_242);
x_269 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_269, 2, x_266);
lean_ctor_set(x_269, 3, x_247);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_251);
lean_ctor_set_uint8(x_269, sizeof(void*)*4 + 1, x_18);
lean_ctor_set_uint8(x_269, sizeof(void*)*4 + 2, x_18);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
}
else
{
uint8_t x_272; 
lean_dec_ref(x_247);
lean_dec_ref(x_242);
x_272 = !lean_is_exclusive(x_259);
if (x_272 == 0)
{
return x_259;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_259, 0);
lean_inc(x_273);
lean_dec(x_259);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_275 = lean_ctor_get(x_253, 0);
x_276 = lean_ctor_get(x_253, 1);
x_277 = lean_ctor_get(x_253, 2);
x_278 = lean_ctor_get(x_253, 3);
x_279 = lean_ctor_get_uint8(x_253, sizeof(void*)*7);
x_280 = lean_ctor_get(x_253, 4);
x_281 = lean_ctor_get(x_253, 5);
x_282 = lean_ctor_get(x_253, 6);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_253);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_add(x_282, x_283);
lean_dec(x_282);
x_285 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_276);
lean_ctor_set(x_285, 2, x_277);
lean_ctor_set(x_285, 3, x_278);
lean_ctor_set(x_285, 4, x_280);
lean_ctor_set(x_285, 5, x_281);
lean_ctor_set(x_285, 6, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*7, x_279);
x_286 = lean_st_ref_set(x_246, x_285);
lean_dec(x_246);
x_287 = l_Lean_Compiler_LCNF_getType(x_245, x_243, x_248, x_249, x_250);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_243);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_289 = x_287;
} else {
 lean_dec_ref(x_287);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_242, 2);
lean_inc_ref(x_290);
x_291 = lean_ctor_get(x_242, 4);
lean_inc_ref(x_291);
lean_dec_ref(x_242);
x_292 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
lean_ctor_set(x_292, 2, x_288);
lean_ctor_set(x_292, 3, x_247);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_251);
lean_ctor_set_uint8(x_292, sizeof(void*)*4 + 1, x_18);
lean_ctor_set_uint8(x_292, sizeof(void*)*4 + 2, x_18);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
if (lean_is_scalar(x_289)) {
 x_294 = lean_alloc_ctor(0, 1, 0);
} else {
 x_294 = x_289;
}
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_247);
lean_dec_ref(x_242);
x_295 = lean_ctor_get(x_287, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_296 = x_287;
} else {
 lean_dec_ref(x_287);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_295);
return x_297;
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
x_298 = !lean_is_exclusive(x_252);
if (x_298 == 0)
{
return x_252;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_252, 0);
lean_inc(x_299);
lean_dec(x_252);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
}
block_326:
{
lean_object* x_312; 
x_312 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_302, x_306, x_303);
if (lean_obj_tag(x_312) == 0)
{
if (x_307 == 0)
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_312, 0);
x_315 = lean_unbox(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_314);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
x_316 = lean_box(0);
lean_ctor_set(x_312, 0, x_316);
return x_312;
}
else
{
uint8_t x_317; 
lean_free_object(x_312);
x_317 = lean_unbox(x_314);
lean_dec(x_314);
x_242 = x_302;
x_243 = x_303;
x_244 = lean_box(0);
x_245 = x_305;
x_246 = x_306;
x_247 = x_309;
x_248 = x_308;
x_249 = x_310;
x_250 = x_311;
x_251 = x_317;
goto block_301;
}
}
else
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_312, 0);
lean_inc(x_318);
lean_dec(x_312);
x_319 = lean_unbox(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_318);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = lean_unbox(x_318);
lean_dec(x_318);
x_242 = x_302;
x_243 = x_303;
x_244 = lean_box(0);
x_245 = x_305;
x_246 = x_306;
x_247 = x_309;
x_248 = x_308;
x_249 = x_310;
x_250 = x_311;
x_251 = x_322;
goto block_301;
}
}
}
else
{
lean_dec_ref(x_312);
x_242 = x_302;
x_243 = x_303;
x_244 = lean_box(0);
x_245 = x_305;
x_246 = x_306;
x_247 = x_309;
x_248 = x_308;
x_249 = x_310;
x_250 = x_311;
x_251 = x_307;
goto block_301;
}
}
else
{
uint8_t x_323; 
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
x_323 = !lean_is_exclusive(x_312);
if (x_323 == 0)
{
return x_312;
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_312, 0);
lean_inc(x_324);
lean_dec(x_312);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
return x_325;
}
}
}
block_360:
{
uint8_t x_336; lean_object* x_337; 
x_336 = 0;
lean_inc(x_327);
x_337 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(x_336, x_327, x_332);
if (lean_obj_tag(x_337) == 0)
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_337);
if (x_338 == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_337, 0);
if (lean_obj_tag(x_339) == 1)
{
if (x_329 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = lean_unsigned_to_nat(0u);
x_342 = lean_array_get_size(x_328);
x_343 = lean_nat_dec_lt(x_341, x_342);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_340);
lean_dec(x_334);
lean_dec_ref(x_333);
lean_dec(x_332);
lean_dec_ref(x_331);
lean_dec(x_330);
lean_dec_ref(x_328);
lean_dec(x_327);
x_344 = lean_box(0);
lean_ctor_set(x_337, 0, x_344);
return x_337;
}
else
{
lean_free_object(x_337);
x_302 = x_340;
x_303 = x_331;
x_304 = lean_box(0);
x_305 = x_327;
x_306 = x_330;
x_307 = x_329;
x_308 = x_332;
x_309 = x_328;
x_310 = x_333;
x_311 = x_334;
goto block_326;
}
}
else
{
lean_object* x_345; 
lean_free_object(x_337);
x_345 = lean_ctor_get(x_339, 0);
lean_inc(x_345);
lean_dec_ref(x_339);
x_302 = x_345;
x_303 = x_331;
x_304 = lean_box(0);
x_305 = x_327;
x_306 = x_330;
x_307 = x_329;
x_308 = x_332;
x_309 = x_328;
x_310 = x_333;
x_311 = x_334;
goto block_326;
}
}
else
{
lean_object* x_346; 
lean_dec(x_339);
lean_dec(x_334);
lean_dec_ref(x_333);
lean_dec(x_332);
lean_dec_ref(x_331);
lean_dec(x_330);
lean_dec_ref(x_328);
lean_dec(x_327);
x_346 = lean_box(0);
lean_ctor_set(x_337, 0, x_346);
return x_337;
}
}
else
{
lean_object* x_347; 
x_347 = lean_ctor_get(x_337, 0);
lean_inc(x_347);
lean_dec(x_337);
if (lean_obj_tag(x_347) == 1)
{
if (x_329 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
lean_dec_ref(x_347);
x_349 = lean_unsigned_to_nat(0u);
x_350 = lean_array_get_size(x_328);
x_351 = lean_nat_dec_lt(x_349, x_350);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_348);
lean_dec(x_334);
lean_dec_ref(x_333);
lean_dec(x_332);
lean_dec_ref(x_331);
lean_dec(x_330);
lean_dec_ref(x_328);
lean_dec(x_327);
x_352 = lean_box(0);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
}
else
{
x_302 = x_348;
x_303 = x_331;
x_304 = lean_box(0);
x_305 = x_327;
x_306 = x_330;
x_307 = x_329;
x_308 = x_332;
x_309 = x_328;
x_310 = x_333;
x_311 = x_334;
goto block_326;
}
}
else
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_347, 0);
lean_inc(x_354);
lean_dec_ref(x_347);
x_302 = x_354;
x_303 = x_331;
x_304 = lean_box(0);
x_305 = x_327;
x_306 = x_330;
x_307 = x_329;
x_308 = x_332;
x_309 = x_328;
x_310 = x_333;
x_311 = x_334;
goto block_326;
}
}
else
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_347);
lean_dec(x_334);
lean_dec_ref(x_333);
lean_dec(x_332);
lean_dec_ref(x_331);
lean_dec(x_330);
lean_dec_ref(x_328);
lean_dec(x_327);
x_355 = lean_box(0);
x_356 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_356, 0, x_355);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_334);
lean_dec_ref(x_333);
lean_dec(x_332);
lean_dec_ref(x_331);
lean_dec(x_330);
lean_dec_ref(x_328);
lean_dec(x_327);
x_357 = !lean_is_exclusive(x_337);
if (x_357 == 0)
{
return x_337;
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_337, 0);
lean_inc(x_358);
lean_dec(x_337);
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_358);
return x_359;
}
}
}
block_378:
{
if (lean_obj_tag(x_361) == 3)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_361, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_361, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_361, 2);
lean_inc_ref(x_373);
lean_dec_ref(x_361);
x_186 = x_371;
x_187 = x_372;
x_188 = x_373;
x_189 = x_362;
x_190 = x_363;
x_191 = x_364;
x_192 = x_365;
x_193 = x_366;
x_194 = x_367;
x_195 = x_368;
x_196 = x_369;
x_197 = lean_box(0);
goto block_241;
}
else
{
lean_dec_ref(x_365);
lean_dec_ref(x_363);
if (lean_obj_tag(x_361) == 4)
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_361, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_361, 1);
lean_inc_ref(x_375);
lean_dec_ref(x_361);
x_327 = x_374;
x_328 = x_375;
x_329 = x_362;
x_330 = x_364;
x_331 = x_366;
x_332 = x_367;
x_333 = x_368;
x_334 = x_369;
x_335 = lean_box(0);
goto block_360;
}
else
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec(x_364);
lean_dec(x_361);
x_376 = lean_box(0);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_376);
return x_377;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__0 = _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__0);
l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__1 = _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__1);
l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2 = _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg___closed__2);
l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0 = _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3___closed__0);
l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3 = _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3();
lean_mark_persistent(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14);
if (builtin) {res = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
