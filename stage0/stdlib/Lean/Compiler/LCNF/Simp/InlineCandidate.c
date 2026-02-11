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
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_override"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instDecidableEqBool"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 149, 37, 168, 195, 83, 72, 87)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`inline` applied to non-local declaration '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`inline` applied to constructor '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.Simp.InlineCandidate"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Simp.inlineCandidate\?"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 120, .m_capacity = 120, .m_length = 119, .m_data = "assertion violation: ( __do_lift._@.Lean.Compiler.LCNF.Simp.InlineCandidate.450150219._hygCtx._hyg.45.0 ).isSome\n      "};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`inline` applied to parameters is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15;
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
uint8_t lean_name_eq(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 182, 14, 42, 67, 101, 187, 98)}};
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0));
x_18 = lean_string_dec_eq(x_16, x_17);
if (x_18 == 0)
{
goto block_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_19 = lean_box(x_3);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_apply_9(x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(54u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_18 = 0;
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_1, 0);
lean_inc(x_361);
if (lean_obj_tag(x_361) == 1)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_361, 0);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_363 = lean_ctor_get(x_1, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_364);
lean_dec_ref(x_1);
x_365 = lean_ctor_get(x_361, 1);
x_366 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2));
x_367 = lean_string_dec_eq(x_365, x_366);
if (x_367 == 0)
{
x_168 = x_361;
x_169 = x_363;
x_170 = x_364;
x_171 = x_18;
x_172 = x_2;
x_173 = x_3;
x_174 = x_4;
x_175 = x_5;
x_176 = x_6;
x_177 = x_7;
x_178 = x_8;
x_179 = lean_box(0);
goto block_223;
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_368 = lean_array_get_size(x_364);
x_369 = lean_unsigned_to_nat(2u);
x_370 = lean_nat_dec_eq(x_368, x_369);
if (x_370 == 0)
{
x_168 = x_361;
x_169 = x_363;
x_170 = x_364;
x_171 = x_18;
x_172 = x_2;
x_173 = x_3;
x_174 = x_4;
x_175 = x_5;
x_176 = x_6;
x_177 = x_7;
x_178 = x_8;
x_179 = lean_box(0);
goto block_223;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_unsigned_to_nat(1u);
x_372 = lean_array_fget_borrowed(x_364, x_371);
if (lean_obj_tag(x_372) == 1)
{
lean_object* x_373; uint8_t x_374; lean_object* x_375; 
lean_inc_ref(x_372);
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_361);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec_ref(x_372);
x_374 = 0;
lean_inc(x_373);
x_375 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(x_374, x_373, x_6);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
if (lean_obj_tag(x_376) == 1)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_373);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_dec_ref(x_376);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec(x_377);
x_379 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3;
x_309 = x_378;
x_310 = x_379;
x_311 = x_370;
x_312 = x_3;
x_313 = x_5;
x_314 = x_6;
x_315 = x_7;
x_316 = x_8;
x_317 = lean_box(0);
goto block_342;
}
else
{
lean_object* x_380; 
lean_dec(x_376);
x_380 = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(x_374, x_373, x_6);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec_ref(x_380);
if (lean_obj_tag(x_381) == 1)
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_373);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
x_383 = lean_ctor_get(x_382, 3);
lean_inc(x_383);
lean_dec(x_382);
if (lean_obj_tag(x_383) == 3)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 2);
lean_inc_ref(x_386);
lean_dec_ref(x_383);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_384);
x_387 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(x_384, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
lean_dec_ref(x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; 
x_389 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = lean_unbox(x_390);
lean_dec(x_390);
x_392 = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(x_384, x_391, x_8);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
if (lean_obj_tag(x_393) == 1)
{
lean_dec_ref(x_393);
x_168 = x_384;
x_169 = x_385;
x_170 = x_386;
x_171 = x_370;
x_172 = x_2;
x_173 = x_3;
x_174 = x_4;
x_175 = x_5;
x_176 = x_6;
x_177 = x_7;
x_178 = x_8;
x_179 = lean_box(0);
goto block_223;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
lean_dec(x_393);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_394 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5;
x_395 = l_Lean_MessageData_ofName(x_384);
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7;
x_398 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_398, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_400 = !lean_is_exclusive(x_399);
if (x_400 == 0)
{
return x_399;
}
else
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
lean_dec(x_399);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_401);
return x_402;
}
}
}
else
{
uint8_t x_403; 
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_403 = !lean_is_exclusive(x_392);
if (x_403 == 0)
{
return x_392;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_392, 0);
lean_inc(x_404);
lean_dec(x_392);
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_406 = !lean_is_exclusive(x_389);
if (x_406 == 0)
{
return x_389;
}
else
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_389, 0);
lean_inc(x_407);
lean_dec(x_389);
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_407);
return x_408;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_dec_ref(x_388);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_409 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9;
x_410 = l_Lean_MessageData_ofName(x_384);
x_411 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7;
x_413 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_413, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
return x_414;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_417, 0, x_416);
return x_417;
}
}
}
else
{
uint8_t x_418; 
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_418 = !lean_is_exclusive(x_387);
if (x_418 == 0)
{
return x_387;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_387, 0);
lean_inc(x_419);
lean_dec(x_387);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
}
}
else
{
x_343 = x_383;
x_344 = x_370;
x_345 = x_2;
x_346 = x_3;
x_347 = x_4;
x_348 = x_5;
x_349 = x_6;
x_350 = x_7;
x_351 = x_8;
x_352 = lean_box(0);
goto block_360;
}
}
else
{
lean_object* x_421; 
lean_dec(x_381);
x_421 = l_Lean_Compiler_LCNF_findParam_x3f___redArg(x_374, x_373, x_6);
lean_dec(x_373);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec_ref(x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; 
x_423 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13;
x_424 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__3(x_423, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec_ref(x_422);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_425 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15;
x_426 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___redArg(x_425, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_427 = !lean_is_exclusive(x_426);
if (x_427 == 0)
{
return x_426;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_430 = !lean_is_exclusive(x_421);
if (x_430 == 0)
{
return x_421;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_421, 0);
lean_inc(x_431);
lean_dec(x_421);
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_431);
return x_432;
}
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_373);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_433 = !lean_is_exclusive(x_380);
if (x_433 == 0)
{
return x_380;
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_380, 0);
lean_inc(x_434);
lean_dec(x_380);
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_373);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_436 = !lean_is_exclusive(x_375);
if (x_436 == 0)
{
return x_375;
}
else
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_375, 0);
lean_inc(x_437);
lean_dec(x_375);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
}
}
else
{
x_168 = x_361;
x_169 = x_363;
x_170 = x_364;
x_171 = x_18;
x_172 = x_2;
x_173 = x_3;
x_174 = x_4;
x_175 = x_5;
x_176 = x_6;
x_177 = x_7;
x_178 = x_8;
x_179 = lean_box(0);
goto block_223;
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_1, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_440);
lean_dec_ref(x_1);
x_168 = x_361;
x_169 = x_439;
x_170 = x_440;
x_171 = x_18;
x_172 = x_2;
x_173 = x_3;
x_174 = x_4;
x_175 = x_5;
x_176 = x_6;
x_177 = x_7;
x_178 = x_8;
x_179 = lean_box(0);
goto block_223;
}
}
else
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_1, 1);
lean_inc(x_441);
x_442 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_442);
lean_dec_ref(x_1);
x_168 = x_361;
x_169 = x_441;
x_170 = x_442;
x_171 = x_18;
x_172 = x_2;
x_173 = x_3;
x_174 = x_4;
x_175 = x_5;
x_176 = x_6;
x_177 = x_7;
x_178 = x_8;
x_179 = lean_box(0);
goto block_223;
}
}
else
{
x_343 = x_1;
x_344 = x_18;
x_345 = x_2;
x_346 = x_3;
x_347 = x_4;
x_348 = x_5;
x_349 = x_6;
x_350 = x_7;
x_351 = x_8;
x_352 = lean_box(0);
goto block_360;
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
lean_inc(x_25);
lean_inc_ref(x_26);
x_33 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_19, x_26, x_25);
lean_inc(x_25);
x_34 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(x_24, x_32, x_25);
x_35 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(x_26, x_25);
x_36 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_21);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_36, sizeof(void*)*4 + 1, x_22);
lean_ctor_set_uint8(x_36, sizeof(void*)*4 + 2, x_20);
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
lean_inc(x_25);
lean_inc_ref(x_26);
x_39 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_19, x_26, x_25);
lean_inc(x_25);
x_40 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(x_24, x_38, x_25);
x_41 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(x_26, x_25);
x_42 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_21);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 1, x_22);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 2, x_20);
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
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
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
if (x_54 == 0)
{
lean_dec(x_56);
lean_dec(x_50);
x_19 = x_49;
x_20 = x_51;
x_21 = x_52;
x_22 = x_54;
x_23 = x_53;
x_24 = x_55;
x_25 = x_57;
x_26 = x_59;
x_27 = x_60;
x_28 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_61; 
lean_inc_ref(x_59);
x_61 = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(x_59);
if (lean_obj_tag(x_61) == 1)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_array_get_size(x_52);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_50);
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
x_68 = lean_array_get_borrowed(x_67, x_52, x_63);
lean_dec(x_63);
x_69 = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(x_68, x_56, x_50);
lean_dec(x_50);
lean_dec(x_56);
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
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_73 = lean_box(0);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_free_object(x_69);
x_19 = x_49;
x_20 = x_51;
x_21 = x_52;
x_22 = x_54;
x_23 = x_53;
x_24 = x_55;
x_25 = x_57;
x_26 = x_59;
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
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
else
{
x_19 = x_49;
x_20 = x_51;
x_21 = x_52;
x_22 = x_54;
x_23 = x_53;
x_24 = x_55;
x_25 = x_57;
x_26 = x_59;
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
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
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
x_82 = lean_array_get_size(x_52);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_50);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_box(0);
x_87 = lean_array_get_borrowed(x_86, x_52, x_81);
lean_dec(x_81);
x_88 = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(x_87, x_56, x_50);
lean_dec(x_50);
lean_dec(x_56);
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
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
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
x_20 = x_51;
x_21 = x_52;
x_22 = x_54;
x_23 = x_53;
x_24 = x_55;
x_25 = x_57;
x_26 = x_59;
x_27 = x_60;
x_28 = lean_box(0);
goto block_48;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
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
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_50);
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
lean_dec_ref(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_102);
x_14 = lean_box(0);
goto block_17;
}
else
{
if (x_110 == 0)
{
if (x_103 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_111);
x_118 = lean_array_get_size(x_104);
x_119 = lean_nat_dec_lt(x_118, x_117);
lean_dec(x_117);
if (x_119 == 0)
{
lean_free_object(x_113);
x_49 = x_101;
x_50 = x_102;
x_51 = x_100;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_111;
x_60 = x_112;
goto block_99;
}
else
{
lean_object* x_120; 
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_102);
x_120 = lean_box(0);
lean_ctor_set(x_113, 0, x_120);
return x_113;
}
}
else
{
lean_free_object(x_113);
x_49 = x_101;
x_50 = x_102;
x_51 = x_100;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_111;
x_60 = x_112;
goto block_99;
}
}
else
{
lean_free_object(x_113);
x_49 = x_101;
x_50 = x_102;
x_51 = x_100;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_111;
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
lean_dec_ref(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_102);
x_14 = lean_box(0);
goto block_17;
}
else
{
if (x_110 == 0)
{
if (x_103 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_111);
x_124 = lean_array_get_size(x_104);
x_125 = lean_nat_dec_lt(x_124, x_123);
lean_dec(x_123);
if (x_125 == 0)
{
x_49 = x_101;
x_50 = x_102;
x_51 = x_100;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_111;
x_60 = x_112;
goto block_99;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_102);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
x_49 = x_101;
x_50 = x_102;
x_51 = x_100;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_111;
x_60 = x_112;
goto block_99;
}
}
else
{
x_49 = x_101;
x_50 = x_102;
x_51 = x_100;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_111;
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
lean_dec_ref(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_102);
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
block_167:
{
if (x_148 == 0)
{
lean_object* x_152; 
x_152 = l_Lean_Compiler_LCNF_inBasePhase___redArg(x_136);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_132);
x_155 = lean_box(0);
lean_inc(x_140);
lean_inc(x_146);
lean_inc(x_150);
x_156 = lean_apply_9(x_134, x_155, x_137, x_150, x_151, x_136, x_146, x_138, x_140, lean_box(0));
x_100 = x_133;
x_101 = x_139;
x_102 = x_140;
x_103 = x_141;
x_104 = x_142;
x_105 = x_143;
x_106 = x_144;
x_107 = x_145;
x_108 = x_146;
x_109 = x_147;
x_110 = x_148;
x_111 = x_149;
x_112 = x_150;
x_113 = x_156;
goto block_131;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec_ref(x_134);
x_157 = lean_ctor_get(x_143, 0);
lean_inc(x_157);
x_158 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___redArg(x_157, x_140);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = lean_unbox(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_box(0);
lean_inc(x_140);
lean_inc(x_146);
lean_inc(x_150);
x_162 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_132, x_157, x_18, x_161, x_137, x_150, x_151, x_136, x_146, x_138, x_140);
x_100 = x_133;
x_101 = x_139;
x_102 = x_140;
x_103 = x_141;
x_104 = x_142;
x_105 = x_143;
x_106 = x_144;
x_107 = x_145;
x_108 = x_146;
x_109 = x_147;
x_110 = x_148;
x_111 = x_149;
x_112 = x_150;
x_113 = x_162;
goto block_131;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1));
x_164 = lean_name_eq(x_157, x_163);
if (x_164 == 0)
{
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec(x_140);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_132);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_box(0);
lean_inc(x_140);
lean_inc(x_146);
lean_inc(x_150);
x_166 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_132, x_157, x_18, x_165, x_137, x_150, x_151, x_136, x_146, x_138, x_140);
x_100 = x_133;
x_101 = x_139;
x_102 = x_140;
x_103 = x_141;
x_104 = x_142;
x_105 = x_143;
x_106 = x_144;
x_107 = x_145;
x_108 = x_146;
x_109 = x_147;
x_110 = x_148;
x_111 = x_149;
x_112 = x_150;
x_113 = x_166;
goto block_131;
}
}
}
}
else
{
lean_dec_ref(x_151);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_134);
lean_dec_ref(x_132);
x_100 = x_133;
x_101 = x_139;
x_102 = x_140;
x_103 = x_141;
x_104 = x_142;
x_105 = x_143;
x_106 = x_144;
x_107 = x_145;
x_108 = x_146;
x_109 = x_147;
x_110 = x_148;
x_111 = x_149;
x_112 = x_150;
x_113 = x_152;
goto block_131;
}
}
else
{
lean_dec_ref(x_151);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_134);
lean_dec_ref(x_132);
x_49 = x_139;
x_50 = x_140;
x_51 = x_133;
x_52 = x_142;
x_53 = x_143;
x_54 = x_144;
x_55 = x_145;
x_56 = x_146;
x_57 = x_147;
x_58 = lean_box(0);
x_59 = x_149;
x_60 = x_150;
goto block_99;
}
}
block_223:
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_172, 1);
x_181 = lean_ctor_get_uint8(x_180, 3);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
else
{
uint8_t x_184; lean_object* x_185; 
x_184 = lean_ctor_get_uint8(x_180, 1);
x_185 = l_Lean_Compiler_LCNF_getPhase___redArg(x_175);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = lean_unbox(x_186);
x_188 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_168, x_187, x_177, x_178);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_188, 0);
if (lean_obj_tag(x_190) == 1)
{
lean_object* x_191; uint8_t x_192; uint8_t x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_unbox(x_186);
lean_dec(x_186);
x_193 = l_Lean_Compiler_LCNF_Phase_toPurity(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 1);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_free_object(x_188);
x_195 = lean_ctor_get(x_191, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get_uint8(x_191, sizeof(void*)*3);
x_197 = lean_ctor_get(x_194, 0);
lean_inc_ref(x_197);
x_198 = lean_box(x_18);
x_199 = lean_box(x_181);
lean_inc_ref(x_197);
lean_inc(x_191);
x_200 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed), 13, 4);
lean_closure_set(x_200, 0, x_191);
lean_closure_set(x_200, 1, x_197);
lean_closure_set(x_200, 2, x_198);
lean_closure_set(x_200, 3, x_199);
x_201 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_191);
if (x_201 == 0)
{
if (x_196 == 0)
{
lean_inc_ref(x_200);
x_132 = x_200;
x_133 = x_196;
x_134 = x_200;
x_135 = lean_box(0);
x_136 = x_175;
x_137 = x_172;
x_138 = x_177;
x_139 = x_193;
x_140 = x_178;
x_141 = x_184;
x_142 = x_170;
x_143 = x_195;
x_144 = x_201;
x_145 = x_197;
x_146 = x_176;
x_147 = x_169;
x_148 = x_171;
x_149 = x_191;
x_150 = x_173;
x_151 = x_174;
goto block_167;
}
else
{
lean_dec_ref(x_200);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_191);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_inc_ref(x_200);
x_132 = x_200;
x_133 = x_196;
x_134 = x_200;
x_135 = lean_box(0);
x_136 = x_175;
x_137 = x_172;
x_138 = x_177;
x_139 = x_193;
x_140 = x_178;
x_141 = x_184;
x_142 = x_170;
x_143 = x_195;
x_144 = x_201;
x_145 = x_197;
x_146 = x_176;
x_147 = x_169;
x_148 = x_171;
x_149 = x_191;
x_150 = x_173;
x_151 = x_174;
goto block_167;
}
}
else
{
lean_object* x_202; 
lean_dec(x_191);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_202 = lean_box(0);
lean_ctor_set(x_188, 0, x_202);
return x_188;
}
}
else
{
lean_dec(x_191);
lean_free_object(x_188);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_free_object(x_188);
lean_dec(x_190);
lean_dec(x_186);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_188, 0);
lean_inc(x_203);
lean_dec(x_188);
if (lean_obj_tag(x_203) == 1)
{
lean_object* x_204; uint8_t x_205; uint8_t x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_unbox(x_186);
lean_dec(x_186);
x_206 = l_Lean_Compiler_LCNF_Phase_toPurity(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_204, 1);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_208 = lean_ctor_get(x_204, 0);
lean_inc_ref(x_208);
x_209 = lean_ctor_get_uint8(x_204, sizeof(void*)*3);
x_210 = lean_ctor_get(x_207, 0);
lean_inc_ref(x_210);
x_211 = lean_box(x_18);
x_212 = lean_box(x_181);
lean_inc_ref(x_210);
lean_inc(x_204);
x_213 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed), 13, 4);
lean_closure_set(x_213, 0, x_204);
lean_closure_set(x_213, 1, x_210);
lean_closure_set(x_213, 2, x_211);
lean_closure_set(x_213, 3, x_212);
x_214 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_204);
if (x_214 == 0)
{
if (x_209 == 0)
{
lean_inc_ref(x_213);
x_132 = x_213;
x_133 = x_209;
x_134 = x_213;
x_135 = lean_box(0);
x_136 = x_175;
x_137 = x_172;
x_138 = x_177;
x_139 = x_206;
x_140 = x_178;
x_141 = x_184;
x_142 = x_170;
x_143 = x_208;
x_144 = x_214;
x_145 = x_210;
x_146 = x_176;
x_147 = x_169;
x_148 = x_171;
x_149 = x_204;
x_150 = x_173;
x_151 = x_174;
goto block_167;
}
else
{
lean_dec_ref(x_213);
lean_dec_ref(x_210);
lean_dec_ref(x_208);
lean_dec(x_204);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_inc_ref(x_213);
x_132 = x_213;
x_133 = x_209;
x_134 = x_213;
x_135 = lean_box(0);
x_136 = x_175;
x_137 = x_172;
x_138 = x_177;
x_139 = x_206;
x_140 = x_178;
x_141 = x_184;
x_142 = x_170;
x_143 = x_208;
x_144 = x_214;
x_145 = x_210;
x_146 = x_176;
x_147 = x_169;
x_148 = x_171;
x_149 = x_204;
x_150 = x_173;
x_151 = x_174;
goto block_167;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_204);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
else
{
lean_dec(x_204);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_203);
lean_dec(x_186);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_186);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
x_217 = !lean_is_exclusive(x_188);
if (x_217 == 0)
{
return x_188;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_188, 0);
lean_inc(x_218);
lean_dec(x_188);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_220 = !lean_is_exclusive(x_185);
if (x_220 == 0)
{
return x_185;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_185, 0);
lean_inc(x_221);
lean_dec(x_185);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
return x_222;
}
}
}
}
block_283:
{
lean_object* x_234; 
x_234 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(x_225);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; uint8_t x_236; 
lean_dec_ref(x_234);
x_235 = lean_st_ref_take(x_225);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_235, 6);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_add(x_237, x_238);
lean_dec(x_237);
lean_ctor_set(x_235, 6, x_239);
x_240 = lean_st_ref_set(x_225, x_235);
lean_dec(x_225);
x_241 = l_Lean_Compiler_LCNF_getType(x_231, x_224, x_230, x_229, x_228);
lean_dec(x_228);
lean_dec_ref(x_229);
lean_dec(x_230);
lean_dec_ref(x_224);
if (lean_obj_tag(x_241) == 0)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_241, 0);
x_244 = lean_ctor_get(x_227, 2);
lean_inc_ref(x_244);
x_245 = lean_ctor_get(x_227, 4);
lean_inc_ref(x_245);
lean_dec_ref(x_227);
x_246 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_243);
lean_ctor_set(x_246, 3, x_226);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_233);
lean_ctor_set_uint8(x_246, sizeof(void*)*4 + 1, x_18);
lean_ctor_set_uint8(x_246, sizeof(void*)*4 + 2, x_18);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_241, 0, x_247);
return x_241;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_248 = lean_ctor_get(x_241, 0);
lean_inc(x_248);
lean_dec(x_241);
x_249 = lean_ctor_get(x_227, 2);
lean_inc_ref(x_249);
x_250 = lean_ctor_get(x_227, 4);
lean_inc_ref(x_250);
lean_dec_ref(x_227);
x_251 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_248);
lean_ctor_set(x_251, 3, x_226);
lean_ctor_set_uint8(x_251, sizeof(void*)*4, x_233);
lean_ctor_set_uint8(x_251, sizeof(void*)*4 + 1, x_18);
lean_ctor_set_uint8(x_251, sizeof(void*)*4 + 2, x_18);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
else
{
uint8_t x_254; 
lean_dec_ref(x_227);
lean_dec_ref(x_226);
x_254 = !lean_is_exclusive(x_241);
if (x_254 == 0)
{
return x_241;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_241, 0);
lean_inc(x_255);
lean_dec(x_241);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_257 = lean_ctor_get(x_235, 0);
x_258 = lean_ctor_get(x_235, 1);
x_259 = lean_ctor_get(x_235, 2);
x_260 = lean_ctor_get(x_235, 3);
x_261 = lean_ctor_get_uint8(x_235, sizeof(void*)*7);
x_262 = lean_ctor_get(x_235, 4);
x_263 = lean_ctor_get(x_235, 5);
x_264 = lean_ctor_get(x_235, 6);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_235);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_add(x_264, x_265);
lean_dec(x_264);
x_267 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_258);
lean_ctor_set(x_267, 2, x_259);
lean_ctor_set(x_267, 3, x_260);
lean_ctor_set(x_267, 4, x_262);
lean_ctor_set(x_267, 5, x_263);
lean_ctor_set(x_267, 6, x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*7, x_261);
x_268 = lean_st_ref_set(x_225, x_267);
lean_dec(x_225);
x_269 = l_Lean_Compiler_LCNF_getType(x_231, x_224, x_230, x_229, x_228);
lean_dec(x_228);
lean_dec_ref(x_229);
lean_dec(x_230);
lean_dec_ref(x_224);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_227, 2);
lean_inc_ref(x_272);
x_273 = lean_ctor_get(x_227, 4);
lean_inc_ref(x_273);
lean_dec_ref(x_227);
x_274 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_270);
lean_ctor_set(x_274, 3, x_226);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_233);
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 1, x_18);
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 2, x_18);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec_ref(x_227);
lean_dec_ref(x_226);
x_277 = lean_ctor_get(x_269, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_278 = x_269;
} else {
 lean_dec_ref(x_269);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
x_280 = !lean_is_exclusive(x_234);
if (x_280 == 0)
{
return x_234;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_234, 0);
lean_inc(x_281);
lean_dec(x_234);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
block_308:
{
lean_object* x_294; 
x_294 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_291, x_287, x_286);
if (lean_obj_tag(x_294) == 0)
{
if (x_285 == 0)
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = lean_unbox(x_296);
if (x_297 == 0)
{
lean_object* x_298; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec(x_289);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
x_298 = lean_box(0);
lean_ctor_set(x_294, 0, x_298);
return x_294;
}
else
{
uint8_t x_299; 
lean_free_object(x_294);
x_299 = lean_unbox(x_296);
lean_dec(x_296);
x_224 = x_286;
x_225 = x_287;
x_226 = x_290;
x_227 = x_291;
x_228 = x_289;
x_229 = x_288;
x_230 = x_292;
x_231 = x_293;
x_232 = lean_box(0);
x_233 = x_299;
goto block_283;
}
}
else
{
lean_object* x_300; uint8_t x_301; 
x_300 = lean_ctor_get(x_294, 0);
lean_inc(x_300);
lean_dec(x_294);
x_301 = lean_unbox(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_300);
lean_dec(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec(x_289);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
x_302 = lean_box(0);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
else
{
uint8_t x_304; 
x_304 = lean_unbox(x_300);
lean_dec(x_300);
x_224 = x_286;
x_225 = x_287;
x_226 = x_290;
x_227 = x_291;
x_228 = x_289;
x_229 = x_288;
x_230 = x_292;
x_231 = x_293;
x_232 = lean_box(0);
x_233 = x_304;
goto block_283;
}
}
}
else
{
lean_dec_ref(x_294);
x_224 = x_286;
x_225 = x_287;
x_226 = x_290;
x_227 = x_291;
x_228 = x_289;
x_229 = x_288;
x_230 = x_292;
x_231 = x_293;
x_232 = lean_box(0);
x_233 = x_285;
goto block_283;
}
}
else
{
uint8_t x_305; 
lean_dec(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec(x_289);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
x_305 = !lean_is_exclusive(x_294);
if (x_305 == 0)
{
return x_294;
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_294, 0);
lean_inc(x_306);
lean_dec(x_294);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
}
}
block_342:
{
uint8_t x_318; lean_object* x_319; 
x_318 = 0;
lean_inc(x_309);
x_319 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(x_318, x_309, x_314);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_319, 0);
if (lean_obj_tag(x_321) == 1)
{
if (x_311 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec_ref(x_321);
x_323 = lean_unsigned_to_nat(0u);
x_324 = lean_array_get_size(x_310);
x_325 = lean_nat_dec_lt(x_323, x_324);
if (x_325 == 0)
{
lean_object* x_326; 
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
x_326 = lean_box(0);
lean_ctor_set(x_319, 0, x_326);
return x_319;
}
else
{
lean_free_object(x_319);
x_284 = lean_box(0);
x_285 = x_311;
x_286 = x_313;
x_287 = x_312;
x_288 = x_315;
x_289 = x_316;
x_290 = x_310;
x_291 = x_322;
x_292 = x_314;
x_293 = x_309;
goto block_308;
}
}
else
{
lean_object* x_327; 
lean_free_object(x_319);
x_327 = lean_ctor_get(x_321, 0);
lean_inc(x_327);
lean_dec_ref(x_321);
x_284 = lean_box(0);
x_285 = x_311;
x_286 = x_313;
x_287 = x_312;
x_288 = x_315;
x_289 = x_316;
x_290 = x_310;
x_291 = x_327;
x_292 = x_314;
x_293 = x_309;
goto block_308;
}
}
else
{
lean_object* x_328; 
lean_dec(x_321);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
x_328 = lean_box(0);
lean_ctor_set(x_319, 0, x_328);
return x_319;
}
}
else
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_319, 0);
lean_inc(x_329);
lean_dec(x_319);
if (lean_obj_tag(x_329) == 1)
{
if (x_311 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec_ref(x_329);
x_331 = lean_unsigned_to_nat(0u);
x_332 = lean_array_get_size(x_310);
x_333 = lean_nat_dec_lt(x_331, x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_330);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
else
{
x_284 = lean_box(0);
x_285 = x_311;
x_286 = x_313;
x_287 = x_312;
x_288 = x_315;
x_289 = x_316;
x_290 = x_310;
x_291 = x_330;
x_292 = x_314;
x_293 = x_309;
goto block_308;
}
}
else
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_329, 0);
lean_inc(x_336);
lean_dec_ref(x_329);
x_284 = lean_box(0);
x_285 = x_311;
x_286 = x_313;
x_287 = x_312;
x_288 = x_315;
x_289 = x_316;
x_290 = x_310;
x_291 = x_336;
x_292 = x_314;
x_293 = x_309;
goto block_308;
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_329);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_338, 0, x_337);
return x_338;
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
x_339 = !lean_is_exclusive(x_319);
if (x_339 == 0)
{
return x_319;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_319, 0);
lean_inc(x_340);
lean_dec(x_319);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
}
block_360:
{
if (lean_obj_tag(x_343) == 3)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_343, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_343, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_343, 2);
lean_inc_ref(x_355);
lean_dec_ref(x_343);
x_168 = x_353;
x_169 = x_354;
x_170 = x_355;
x_171 = x_344;
x_172 = x_345;
x_173 = x_346;
x_174 = x_347;
x_175 = x_348;
x_176 = x_349;
x_177 = x_350;
x_178 = x_351;
x_179 = lean_box(0);
goto block_223;
}
else
{
lean_dec_ref(x_347);
lean_dec_ref(x_345);
if (lean_obj_tag(x_343) == 4)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_343, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_343, 1);
lean_inc_ref(x_357);
lean_dec_ref(x_343);
x_309 = x_356;
x_310 = x_357;
x_311 = x_344;
x_312 = x_346;
x_313 = x_348;
x_314 = x_349;
x_315 = x_350;
x_316 = x_351;
x_317 = lean_box(0);
goto block_342;
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_351);
lean_dec_ref(x_350);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec(x_346);
lean_dec(x_343);
x_358 = lean_box(0);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_358);
return x_359;
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
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15);
if (builtin) {res = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
