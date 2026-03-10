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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_override"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value;
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3;
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instDecidableEqBool"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 149, 37, 168, 195, 83, 72, 87)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`inline` applied to non-local declaration '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`inline` applied to constructor '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.Simp.InlineCandidate"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Simp.inlineCandidate\?"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 120, .m_data = "assertion violation: ( __do_lift._@.Lean.Compiler.LCNF.Simp.InlineCandidate.450150219._hygCtx._hyg.344.0 ).isSome\n      "};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`inline` applied to parameters is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
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
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object*);
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
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_34; 
x_12 = lean_ctor_get(x_11, 0);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
x_13 = x_11;
x_14 = x_34;
goto block_33;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_31; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 0);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_10, 1);
lean_dec(x_32);
x_17 = x_10;
x_18 = x_31;
goto block_30;
}
else
{
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_31;
goto block_30;
}
block_30:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unbox(x_12);
lean_dec(x_12);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16, x_19);
lean_dec_ref(x_16);
x_21 = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2);
lean_inc_ref(x_7);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_7);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_1);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_11, 0);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
x_36 = x_11;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_76; 
x_10 = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_13 = x_11;
x_14 = x_76;
goto block_75;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_73; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 1);
lean_dec(x_74);
x_19 = x_12;
x_20 = x_73;
goto block_72;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1));
x_22 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_28);
lean_ctor_set(x_71, 3, x_27);
lean_ctor_set(x_71, 4, x_26);
x_29 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_22);
x_30 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_66; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_31, 1);
lean_dec(x_67);
x_33 = x_31;
x_34 = x_66;
goto block_65;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_32, 1);
lean_dec(x_64);
x_39 = x_32;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3));
x_42 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_47);
lean_ctor_set(x_61, 4, x_46);
x_49 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_42);
x_50 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = lean_box(0);
x_54 = l_instInhabitedOfMonad___redArg(x_52, x_53);
x_55 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_panic_fn(x_55, x_1);
x_57 = lean_apply_8(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_57;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(x_1);
if (x_16 == 0)
{
if (x_2 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(x_1);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(x_3, x_10);
return x_18;
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
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(x_5);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(x_5);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_5);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_4);
x_17 = lean_unbox(x_5);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(x_1, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_18;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_104; 
x_10 = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_104 = !lean_is_exclusive(x_11);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_11, 1);
lean_dec(x_105);
x_13 = x_11;
x_14 = x_104;
goto block_103;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_101; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_101 = !lean_is_exclusive(x_12);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_12, 1);
lean_dec(x_102);
x_19 = x_12;
x_20 = x_101;
goto block_100;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1));
x_22 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_25);
lean_ctor_set(x_99, 1, x_21);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_27);
lean_ctor_set(x_99, 4, x_26);
x_29 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_29);
lean_ctor_set(x_97, 1, x_22);
x_30 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_94; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_94 = !lean_is_exclusive(x_31);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_31, 1);
lean_dec(x_95);
x_33 = x_31;
x_34 = x_94;
goto block_93;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_91; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_91 = !lean_is_exclusive(x_32);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_32, 1);
lean_dec(x_92);
x_39 = x_32;
x_40 = x_91;
goto block_90;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3));
x_42 = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_45);
lean_ctor_set(x_89, 1, x_41);
lean_ctor_set(x_89, 2, x_48);
lean_ctor_set(x_89, 3, x_47);
lean_ctor_set(x_89, 4, x_46);
x_49 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_49);
lean_ctor_set(x_87, 1, x_42);
x_50 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_84; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = lean_ctor_get(x_52, 0);
x_84 = !lean_is_exclusive(x_52);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_52, 1);
lean_dec(x_85);
x_54 = x_52;
x_55 = x_84;
goto block_83;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_81; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 2);
x_58 = lean_ctor_get(x_53, 3);
x_59 = lean_ctor_get(x_53, 4);
x_81 = !lean_is_exclusive(x_53);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_53, 1);
lean_dec(x_82);
x_60 = x_53;
x_61 = x_81;
goto block_80;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_53);
x_60 = lean_box(0);
x_61 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0));
x_63 = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1));
lean_inc_ref(x_56);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_64, 0, x_56);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_65, 0, x_56);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_67, 0, x_59);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_68, 0, x_58);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_69, 0, x_57);
if (x_61 == 0)
{
lean_ctor_set(x_60, 4, x_67);
lean_ctor_set(x_60, 3, x_68);
lean_ctor_set(x_60, 2, x_69);
lean_ctor_set(x_60, 1, x_62);
lean_ctor_set(x_60, 0, x_66);
x_70 = x_60;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_62);
lean_ctor_set(x_79, 2, x_69);
lean_ctor_set(x_79, 3, x_68);
lean_ctor_set(x_79, 4, x_67);
x_70 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_71; 
if (x_55 == 0)
{
lean_ctor_set(x_54, 1, x_63);
lean_ctor_set(x_54, 0, x_70);
x_71 = x_54;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_63);
x_71 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_box(0);
x_73 = l_instInhabitedOfMonad___redArg(x_71, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_8(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_75;
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
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(122u);
x_4 = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1));
x_5 = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_18 = x_16;
x_19 = x_36;
goto block_35;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
if (x_20 == 6)
{
lean_object* x_21; 
x_21 = l_Lean_AsyncConstantInfo_toConstantInfo(x_17);
if (lean_obj_tag(x_21) == 6)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 0);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
x_23 = x_21;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_25; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_22);
x_25 = x_18;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_21);
lean_del_object(x_18);
x_33 = lean_obj_once(&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3, &l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once, _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3);
x_34 = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_34;
}
}
else
{
lean_del_object(x_18);
lean_dec(x_17);
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
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13(void) {
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15(void) {
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
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_16 = 0;
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_1, 0);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 1)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_368, 0);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_370 = lean_ctor_get(x_1, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_371);
lean_dec_ref(x_1);
x_372 = lean_ctor_get(x_368, 1);
x_373 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2));
x_374 = lean_string_dec_eq(x_372, x_373);
if (x_374 == 0)
{
x_167 = x_368;
x_168 = x_370;
x_169 = x_371;
x_170 = x_16;
x_171 = x_2;
x_172 = x_3;
x_173 = x_4;
x_174 = x_5;
x_175 = x_6;
x_176 = x_7;
x_177 = x_8;
goto block_224;
}
else
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = lean_array_get_size(x_371);
x_376 = lean_unsigned_to_nat(2u);
x_377 = lean_nat_dec_eq(x_375, x_376);
if (x_377 == 0)
{
x_167 = x_368;
x_168 = x_370;
x_169 = x_371;
x_170 = x_16;
x_171 = x_2;
x_172 = x_3;
x_173 = x_4;
x_174 = x_5;
x_175 = x_6;
x_176 = x_7;
x_177 = x_8;
goto block_224;
}
else
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_array_fget_borrowed(x_371, x_378);
if (lean_obj_tag(x_379) == 1)
{
lean_object* x_380; uint8_t x_381; lean_object* x_382; 
lean_inc_ref(x_379);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_368);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec_ref(x_379);
x_381 = 0;
lean_inc(x_380);
x_382 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(x_381, x_380, x_6);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec_ref(x_382);
if (lean_obj_tag(x_383) == 1)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_380);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
lean_dec_ref(x_383);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec(x_384);
x_386 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3));
x_314 = x_385;
x_315 = x_386;
x_316 = x_377;
x_317 = x_3;
x_318 = x_5;
x_319 = x_6;
x_320 = x_7;
x_321 = x_8;
goto block_350;
}
else
{
lean_object* x_387; 
lean_dec(x_383);
x_387 = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(x_381, x_380, x_6);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
lean_dec_ref(x_387);
if (lean_obj_tag(x_388) == 1)
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_380);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
x_390 = lean_ctor_get(x_389, 3);
lean_inc(x_390);
lean_dec(x_389);
if (lean_obj_tag(x_390) == 3)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_390, 2);
lean_inc_ref(x_393);
lean_dec_ref(x_390);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_391);
x_394 = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(x_391, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; 
x_396 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
x_399 = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(x_391, x_398, x_8);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
if (lean_obj_tag(x_400) == 1)
{
lean_dec_ref(x_400);
x_167 = x_391;
x_168 = x_392;
x_169 = x_393;
x_170 = x_377;
x_171 = x_2;
x_172 = x_3;
x_173 = x_4;
x_174 = x_5;
x_175 = x_6;
x_176 = x_7;
x_177 = x_8;
goto block_224;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; uint8_t x_414; 
lean_dec(x_400);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_401 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5);
x_402 = l_Lean_MessageData_ofName(x_391);
x_403 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
x_405 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
x_406 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(x_405, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_407 = lean_ctor_get(x_406, 0);
x_414 = !lean_is_exclusive(x_406);
if (x_414 == 0)
{
x_408 = x_406;
x_409 = x_414;
goto block_413;
}
else
{
lean_inc(x_407);
lean_dec(x_406);
x_408 = lean_box(0);
x_409 = x_414;
goto block_413;
}
block_413:
{
lean_object* x_410; 
if (x_409 == 0)
{
x_410 = x_408;
goto block_411;
}
else
{
lean_object* x_412; 
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_407);
x_410 = x_412;
goto block_411;
}
block_411:
{
return x_410;
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; uint8_t x_422; 
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_415 = lean_ctor_get(x_399, 0);
x_422 = !lean_is_exclusive(x_399);
if (x_422 == 0)
{
x_416 = x_399;
x_417 = x_422;
goto block_421;
}
else
{
lean_inc(x_415);
lean_dec(x_399);
x_416 = lean_box(0);
x_417 = x_422;
goto block_421;
}
block_421:
{
lean_object* x_418; 
if (x_417 == 0)
{
x_418 = x_416;
goto block_419;
}
else
{
lean_object* x_420; 
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_415);
x_418 = x_420;
goto block_419;
}
block_419:
{
return x_418;
}
}
}
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; uint8_t x_430; 
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_423 = lean_ctor_get(x_396, 0);
x_430 = !lean_is_exclusive(x_396);
if (x_430 == 0)
{
x_424 = x_396;
x_425 = x_430;
goto block_429;
}
else
{
lean_inc(x_423);
lean_dec(x_396);
x_424 = lean_box(0);
x_425 = x_430;
goto block_429;
}
block_429:
{
lean_object* x_426; 
if (x_425 == 0)
{
x_426 = x_424;
goto block_427;
}
else
{
lean_object* x_428; 
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_423);
x_426 = x_428;
goto block_427;
}
block_427:
{
return x_426;
}
}
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_444; 
lean_dec_ref(x_395);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_431 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9);
x_432 = l_Lean_MessageData_ofName(x_391);
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
x_435 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
x_436 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(x_435, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_437 = lean_ctor_get(x_436, 0);
x_444 = !lean_is_exclusive(x_436);
if (x_444 == 0)
{
x_438 = x_436;
x_439 = x_444;
goto block_443;
}
else
{
lean_inc(x_437);
lean_dec(x_436);
x_438 = lean_box(0);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_439 == 0)
{
x_440 = x_438;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_437);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
else
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; uint8_t x_452; 
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_445 = lean_ctor_get(x_394, 0);
x_452 = !lean_is_exclusive(x_394);
if (x_452 == 0)
{
x_446 = x_394;
x_447 = x_452;
goto block_451;
}
else
{
lean_inc(x_445);
lean_dec(x_394);
x_446 = lean_box(0);
x_447 = x_452;
goto block_451;
}
block_451:
{
lean_object* x_448; 
if (x_447 == 0)
{
x_448 = x_446;
goto block_449;
}
else
{
lean_object* x_450; 
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_445);
x_448 = x_450;
goto block_449;
}
block_449:
{
return x_448;
}
}
}
}
else
{
x_351 = x_390;
x_352 = x_377;
x_353 = x_2;
x_354 = x_3;
x_355 = x_4;
x_356 = x_5;
x_357 = x_6;
x_358 = x_7;
x_359 = x_8;
goto block_367;
}
}
else
{
lean_object* x_453; 
lean_dec(x_388);
x_453 = l_Lean_Compiler_LCNF_findParam_x3f___redArg(x_381, x_380, x_6);
lean_dec(x_380);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
lean_dec_ref(x_453);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13);
x_456 = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(x_455, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; uint8_t x_466; 
lean_dec_ref(x_454);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_457 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15);
x_458 = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(x_457, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_459 = lean_ctor_get(x_458, 0);
x_466 = !lean_is_exclusive(x_458);
if (x_466 == 0)
{
x_460 = x_458;
x_461 = x_466;
goto block_465;
}
else
{
lean_inc(x_459);
lean_dec(x_458);
x_460 = lean_box(0);
x_461 = x_466;
goto block_465;
}
block_465:
{
lean_object* x_462; 
if (x_461 == 0)
{
x_462 = x_460;
goto block_463;
}
else
{
lean_object* x_464; 
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_459);
x_462 = x_464;
goto block_463;
}
block_463:
{
return x_462;
}
}
}
}
else
{
lean_object* x_467; lean_object* x_468; uint8_t x_469; uint8_t x_474; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_467 = lean_ctor_get(x_453, 0);
x_474 = !lean_is_exclusive(x_453);
if (x_474 == 0)
{
x_468 = x_453;
x_469 = x_474;
goto block_473;
}
else
{
lean_inc(x_467);
lean_dec(x_453);
x_468 = lean_box(0);
x_469 = x_474;
goto block_473;
}
block_473:
{
lean_object* x_470; 
if (x_469 == 0)
{
x_470 = x_468;
goto block_471;
}
else
{
lean_object* x_472; 
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_467);
x_470 = x_472;
goto block_471;
}
block_471:
{
return x_470;
}
}
}
}
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; uint8_t x_482; 
lean_dec(x_380);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_475 = lean_ctor_get(x_387, 0);
x_482 = !lean_is_exclusive(x_387);
if (x_482 == 0)
{
x_476 = x_387;
x_477 = x_482;
goto block_481;
}
else
{
lean_inc(x_475);
lean_dec(x_387);
x_476 = lean_box(0);
x_477 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_478; 
if (x_477 == 0)
{
x_478 = x_476;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_475);
x_478 = x_480;
goto block_479;
}
block_479:
{
return x_478;
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_490; 
lean_dec(x_380);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_483 = lean_ctor_get(x_382, 0);
x_490 = !lean_is_exclusive(x_382);
if (x_490 == 0)
{
x_484 = x_382;
x_485 = x_490;
goto block_489;
}
else
{
lean_inc(x_483);
lean_dec(x_382);
x_484 = lean_box(0);
x_485 = x_490;
goto block_489;
}
block_489:
{
lean_object* x_486; 
if (x_485 == 0)
{
x_486 = x_484;
goto block_487;
}
else
{
lean_object* x_488; 
x_488 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_488, 0, x_483);
x_486 = x_488;
goto block_487;
}
block_487:
{
return x_486;
}
}
}
}
else
{
x_167 = x_368;
x_168 = x_370;
x_169 = x_371;
x_170 = x_16;
x_171 = x_2;
x_172 = x_3;
x_173 = x_4;
x_174 = x_5;
x_175 = x_6;
x_176 = x_7;
x_177 = x_8;
goto block_224;
}
}
}
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_1, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_492);
lean_dec_ref(x_1);
x_167 = x_368;
x_168 = x_491;
x_169 = x_492;
x_170 = x_16;
x_171 = x_2;
x_172 = x_3;
x_173 = x_4;
x_174 = x_5;
x_175 = x_6;
x_176 = x_7;
x_177 = x_8;
goto block_224;
}
}
else
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_1, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_494);
lean_dec_ref(x_1);
x_167 = x_368;
x_168 = x_493;
x_169 = x_494;
x_170 = x_16;
x_171 = x_2;
x_172 = x_3;
x_173 = x_4;
x_174 = x_5;
x_175 = x_6;
x_176 = x_7;
x_177 = x_8;
goto block_224;
}
}
else
{
x_351 = x_1;
x_352 = x_16;
x_353 = x_2;
x_354 = x_3;
x_355 = x_4;
x_356 = x_5;
x_357 = x_6;
x_358 = x_7;
x_359 = x_8;
goto block_367;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_49:
{
lean_object* x_26; 
x_26 = l_Lean_Compiler_LCNF_Simp_incInline___redArg(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_26, 0);
lean_dec(x_40);
x_27 = x_26;
x_28 = x_39;
goto block_38;
}
else
{
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec_ref(x_23);
lean_inc(x_19);
lean_inc_ref(x_17);
x_30 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_21, x_17, x_19);
lean_inc(x_19);
x_31 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(x_24, x_29, x_19);
x_32 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(x_17, x_19);
x_33 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_18);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_16);
lean_ctor_set_uint8(x_33, sizeof(void*)*4 + 1, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*4 + 2, x_20);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_34);
x_35 = x_27;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
x_41 = lean_ctor_get(x_26, 0);
x_48 = !lean_is_exclusive(x_26);
if (x_48 == 0)
{
x_42 = x_26;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
block_96:
{
if (x_56 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
x_17 = x_50;
x_18 = x_53;
x_19 = x_52;
x_20 = x_54;
x_21 = x_55;
x_22 = x_56;
x_23 = x_58;
x_24 = x_60;
x_25 = x_51;
goto block_49;
}
else
{
lean_object* x_61; 
lean_inc_ref(x_50);
x_61 = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(x_50);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_93; 
x_62 = lean_ctor_get(x_61, 0);
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
x_63 = x_61;
x_64 = x_93;
goto block_92;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_array_get_size(x_53);
x_66 = lean_nat_dec_lt(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_67 = lean_box(0);
if (x_64 == 0)
{
lean_ctor_set_tag(x_63, 0);
lean_ctor_set(x_63, 0, x_67);
x_68 = x_63;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_del_object(x_63);
x_71 = lean_box(0);
x_72 = lean_array_get_borrowed(x_71, x_53, x_62);
lean_dec(x_62);
x_73 = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(x_72, x_59, x_57);
lean_dec(x_57);
lean_dec(x_59);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_83; 
x_74 = lean_ctor_get(x_73, 0);
x_83 = !lean_is_exclusive(x_73);
if (x_83 == 0)
{
x_75 = x_73;
x_76 = x_83;
goto block_82;
}
else
{
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = x_83;
goto block_82;
}
block_82:
{
uint8_t x_77; 
x_77 = lean_unbox(x_74);
lean_dec(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_78 = lean_box(0);
if (x_76 == 0)
{
lean_ctor_set(x_75, 0, x_78);
x_79 = x_75;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_78);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
else
{
lean_del_object(x_75);
x_17 = x_50;
x_18 = x_53;
x_19 = x_52;
x_20 = x_54;
x_21 = x_55;
x_22 = x_56;
x_23 = x_58;
x_24 = x_60;
x_25 = x_51;
goto block_49;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_84 = lean_ctor_get(x_73, 0);
x_91 = !lean_is_exclusive(x_73);
if (x_91 == 0)
{
x_85 = x_73;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_73);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
block_132:
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_123; 
x_111 = lean_ctor_get(x_110, 0);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
x_112 = x_110;
x_113 = x_123;
goto block_122;
}
else
{
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = x_123;
goto block_122;
}
block_122:
{
uint8_t x_114; 
x_114 = lean_unbox(x_111);
lean_dec(x_111);
if (x_114 == 0)
{
lean_del_object(x_112);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
goto block_12;
}
else
{
if (x_107 == 0)
{
if (x_101 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_100);
x_116 = lean_array_get_size(x_103);
x_117 = lean_nat_dec_lt(x_116, x_115);
lean_dec(x_115);
if (x_117 == 0)
{
lean_del_object(x_112);
x_50 = x_100;
x_51 = x_97;
x_52 = x_102;
x_53 = x_103;
x_54 = x_104;
x_55 = x_105;
x_56 = x_106;
x_57 = x_98;
x_58 = x_108;
x_59 = x_99;
x_60 = x_109;
goto block_96;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_118 = lean_box(0);
if (x_113 == 0)
{
lean_ctor_set(x_112, 0, x_118);
x_119 = x_112;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
else
{
lean_del_object(x_112);
x_50 = x_100;
x_51 = x_97;
x_52 = x_102;
x_53 = x_103;
x_54 = x_104;
x_55 = x_105;
x_56 = x_106;
x_57 = x_98;
x_58 = x_108;
x_59 = x_99;
x_60 = x_109;
goto block_96;
}
}
else
{
lean_del_object(x_112);
x_50 = x_100;
x_51 = x_97;
x_52 = x_102;
x_53 = x_103;
x_54 = x_104;
x_55 = x_105;
x_56 = x_106;
x_57 = x_98;
x_58 = x_108;
x_59 = x_99;
x_60 = x_109;
goto block_96;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_124 = lean_ctor_get(x_110, 0);
x_131 = !lean_is_exclusive(x_110);
if (x_131 == 0)
{
x_125 = x_110;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_dec(x_110);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
block_166:
{
if (x_149 == 0)
{
lean_object* x_151; 
x_151 = l_Lean_Compiler_LCNF_inBasePhase___redArg(x_142);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_box(0);
lean_inc(x_137);
lean_inc(x_138);
lean_inc(x_136);
x_155 = lean_apply_9(x_134, x_154, x_144, x_136, x_147, x_142, x_138, x_139, x_137, lean_box(0));
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_140;
x_101 = x_141;
x_102 = x_145;
x_103 = x_143;
x_104 = x_146;
x_105 = x_148;
x_106 = x_133;
x_107 = x_149;
x_108 = x_150;
x_109 = x_135;
x_110 = x_155;
goto block_132;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_150, 0);
x_157 = l_Lean_Meta_isInstance___redArg(x_156, x_137);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_box(0);
lean_inc(x_137);
lean_inc(x_138);
lean_inc(x_136);
x_161 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_134, x_156, x_16, x_160, x_144, x_136, x_147, x_142, x_138, x_139, x_137);
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_140;
x_101 = x_141;
x_102 = x_145;
x_103 = x_143;
x_104 = x_146;
x_105 = x_148;
x_106 = x_133;
x_107 = x_149;
x_108 = x_150;
x_109 = x_135;
x_110 = x_161;
goto block_132;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1));
x_163 = lean_name_eq(x_156, x_162);
if (x_163 == 0)
{
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
goto block_12;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_box(0);
lean_inc(x_137);
lean_inc(x_138);
lean_inc(x_136);
x_165 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_134, x_156, x_16, x_164, x_144, x_136, x_147, x_142, x_138, x_139, x_137);
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_140;
x_101 = x_141;
x_102 = x_145;
x_103 = x_143;
x_104 = x_146;
x_105 = x_148;
x_106 = x_133;
x_107 = x_149;
x_108 = x_150;
x_109 = x_135;
x_110 = x_165;
goto block_132;
}
}
}
else
{
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec_ref(x_142);
lean_dec_ref(x_139);
lean_dec_ref(x_134);
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_140;
x_101 = x_141;
x_102 = x_145;
x_103 = x_143;
x_104 = x_146;
x_105 = x_148;
x_106 = x_133;
x_107 = x_149;
x_108 = x_150;
x_109 = x_135;
x_110 = x_157;
goto block_132;
}
}
}
else
{
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec_ref(x_142);
lean_dec_ref(x_139);
lean_dec_ref(x_134);
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_140;
x_101 = x_141;
x_102 = x_145;
x_103 = x_143;
x_104 = x_146;
x_105 = x_148;
x_106 = x_133;
x_107 = x_149;
x_108 = x_150;
x_109 = x_135;
x_110 = x_151;
goto block_132;
}
}
else
{
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec_ref(x_142);
lean_dec_ref(x_139);
lean_dec_ref(x_134);
x_50 = x_140;
x_51 = x_136;
x_52 = x_145;
x_53 = x_143;
x_54 = x_146;
x_55 = x_148;
x_56 = x_133;
x_57 = x_137;
x_58 = x_150;
x_59 = x_138;
x_60 = x_135;
goto block_96;
}
}
block_224:
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_171, 1);
x_179 = lean_ctor_get_uint8(x_178, 3);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec(x_167);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
else
{
uint8_t x_182; lean_object* x_183; 
x_182 = lean_ctor_get_uint8(x_178, 1);
x_183 = l_Lean_Compiler_LCNF_getPhase___redArg(x_174);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_unbox(x_184);
x_186 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_167, x_185, x_176, x_177);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_207; 
x_187 = lean_ctor_get(x_186, 0);
x_207 = !lean_is_exclusive(x_186);
if (x_207 == 0)
{
x_188 = x_186;
x_189 = x_207;
goto block_206;
}
else
{
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_box(0);
x_189 = x_207;
goto block_206;
}
block_206:
{
if (lean_obj_tag(x_187) == 1)
{
lean_object* x_190; uint8_t x_191; uint8_t x_192; 
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec_ref(x_187);
x_191 = lean_unbox(x_184);
lean_dec(x_184);
x_192 = l_Lean_Compiler_LCNF_Phase_toPurity(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_190, 1);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_del_object(x_188);
x_194 = lean_ctor_get(x_190, 0);
lean_inc_ref(x_194);
x_195 = lean_ctor_get_uint8(x_190, sizeof(void*)*3);
x_196 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_196);
x_197 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_190);
x_198 = lean_box(x_197);
x_199 = lean_box(x_16);
x_200 = lean_box(x_179);
lean_inc_ref(x_196);
lean_inc(x_190);
x_201 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed), 14, 5);
lean_closure_set(x_201, 0, x_190);
lean_closure_set(x_201, 1, x_198);
lean_closure_set(x_201, 2, x_196);
lean_closure_set(x_201, 3, x_199);
lean_closure_set(x_201, 4, x_200);
if (x_197 == 0)
{
if (x_195 == 0)
{
x_133 = x_197;
x_134 = x_201;
x_135 = x_196;
x_136 = x_172;
x_137 = x_177;
x_138 = x_175;
x_139 = x_176;
x_140 = x_190;
x_141 = x_182;
x_142 = x_174;
x_143 = x_169;
x_144 = x_171;
x_145 = x_168;
x_146 = x_195;
x_147 = x_173;
x_148 = x_192;
x_149 = x_170;
x_150 = x_194;
goto block_166;
}
else
{
lean_dec_ref(x_201);
lean_dec_ref(x_196);
lean_dec_ref(x_194);
lean_dec(x_190);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
goto block_12;
}
}
else
{
x_133 = x_197;
x_134 = x_201;
x_135 = x_196;
x_136 = x_172;
x_137 = x_177;
x_138 = x_175;
x_139 = x_176;
x_140 = x_190;
x_141 = x_182;
x_142 = x_174;
x_143 = x_169;
x_144 = x_171;
x_145 = x_168;
x_146 = x_195;
x_147 = x_173;
x_148 = x_192;
x_149 = x_170;
x_150 = x_194;
goto block_166;
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_190);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
x_202 = lean_box(0);
if (x_189 == 0)
{
lean_ctor_set(x_188, 0, x_202);
x_203 = x_188;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_202);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
else
{
lean_dec(x_190);
lean_del_object(x_188);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
goto block_15;
}
}
else
{
lean_del_object(x_188);
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
goto block_15;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_215; 
lean_dec(x_184);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
x_208 = lean_ctor_get(x_186, 0);
x_215 = !lean_is_exclusive(x_186);
if (x_215 == 0)
{
x_209 = x_186;
x_210 = x_215;
goto block_214;
}
else
{
lean_inc(x_208);
lean_dec(x_186);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_223; 
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec(x_167);
x_216 = lean_ctor_get(x_183, 0);
x_223 = !lean_is_exclusive(x_183);
if (x_223 == 0)
{
x_217 = x_183;
x_218 = x_223;
goto block_222;
}
else
{
lean_inc(x_216);
lean_dec(x_183);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
}
block_283:
{
lean_object* x_234; 
x_234 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_274; 
lean_dec_ref(x_234);
x_235 = lean_st_ref_take(x_233);
x_236 = lean_ctor_get(x_235, 0);
x_237 = lean_ctor_get(x_235, 1);
x_238 = lean_ctor_get(x_235, 2);
x_239 = lean_ctor_get(x_235, 3);
x_240 = lean_ctor_get_uint8(x_235, sizeof(void*)*7);
x_241 = lean_ctor_get(x_235, 4);
x_242 = lean_ctor_get(x_235, 5);
x_243 = lean_ctor_get(x_235, 6);
x_274 = !lean_is_exclusive(x_235);
if (x_274 == 0)
{
x_244 = x_235;
x_245 = x_274;
goto block_273;
}
else
{
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_235);
x_244 = lean_box(0);
x_245 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_243, x_246);
lean_dec(x_243);
if (x_245 == 0)
{
lean_ctor_set(x_244, 6, x_247);
x_248 = x_244;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_272, 0, x_236);
lean_ctor_set(x_272, 1, x_237);
lean_ctor_set(x_272, 2, x_238);
lean_ctor_set(x_272, 3, x_239);
lean_ctor_set(x_272, 4, x_241);
lean_ctor_set(x_272, 5, x_242);
lean_ctor_set(x_272, 6, x_247);
lean_ctor_set_uint8(x_272, sizeof(void*)*7, x_240);
x_248 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_st_ref_set(x_233, x_248);
lean_dec(x_233);
x_250 = l_Lean_Compiler_LCNF_getType(x_225, x_230, x_226, x_229, x_228);
lean_dec(x_228);
lean_dec_ref(x_229);
lean_dec(x_226);
lean_dec_ref(x_230);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_262; 
x_251 = lean_ctor_get(x_250, 0);
x_262 = !lean_is_exclusive(x_250);
if (x_262 == 0)
{
x_252 = x_250;
x_253 = x_262;
goto block_261;
}
else
{
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_box(0);
x_253 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_227, 2);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_227, 4);
lean_inc_ref(x_255);
lean_dec_ref(x_227);
x_256 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
lean_ctor_set(x_256, 2, x_251);
lean_ctor_set(x_256, 3, x_231);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_232);
lean_ctor_set_uint8(x_256, sizeof(void*)*4 + 1, x_16);
lean_ctor_set_uint8(x_256, sizeof(void*)*4 + 2, x_16);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
if (x_253 == 0)
{
lean_ctor_set(x_252, 0, x_257);
x_258 = x_252;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_257);
x_258 = x_260;
goto block_259;
}
block_259:
{
return x_258;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_270; 
lean_dec_ref(x_231);
lean_dec_ref(x_227);
x_263 = lean_ctor_get(x_250, 0);
x_270 = !lean_is_exclusive(x_250);
if (x_270 == 0)
{
x_264 = x_250;
x_265 = x_270;
goto block_269;
}
else
{
lean_inc(x_263);
lean_dec(x_250);
x_264 = lean_box(0);
x_265 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_266; 
if (x_265 == 0)
{
x_266 = x_264;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_263);
x_266 = x_268;
goto block_267;
}
block_267:
{
return x_266;
}
}
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_282; 
lean_dec(x_233);
lean_dec_ref(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec(x_225);
x_275 = lean_ctor_get(x_234, 0);
x_282 = !lean_is_exclusive(x_234);
if (x_282 == 0)
{
x_276 = x_234;
x_277 = x_282;
goto block_281;
}
else
{
lean_inc(x_275);
lean_dec(x_234);
x_276 = lean_box(0);
x_277 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_278; 
if (x_277 == 0)
{
x_278 = x_276;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_275);
x_278 = x_280;
goto block_279;
}
block_279:
{
return x_278;
}
}
}
}
block_313:
{
lean_object* x_293; 
x_293 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_287, x_292, x_290);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_304; 
x_294 = lean_ctor_get(x_293, 0);
x_304 = !lean_is_exclusive(x_293);
if (x_304 == 0)
{
x_295 = x_293;
x_296 = x_304;
goto block_303;
}
else
{
lean_inc(x_294);
lean_dec(x_293);
x_295 = lean_box(0);
x_296 = x_304;
goto block_303;
}
block_303:
{
uint8_t x_297; 
x_297 = 1;
if (x_286 == 0)
{
uint8_t x_298; 
x_298 = lean_unbox(x_294);
lean_dec(x_294);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec_ref(x_287);
lean_dec(x_285);
lean_dec(x_284);
x_299 = lean_box(0);
if (x_296 == 0)
{
lean_ctor_set(x_295, 0, x_299);
x_300 = x_295;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_302, 0, x_299);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
else
{
lean_del_object(x_295);
x_225 = x_284;
x_226 = x_285;
x_227 = x_287;
x_228 = x_288;
x_229 = x_289;
x_230 = x_290;
x_231 = x_291;
x_232 = x_297;
x_233 = x_292;
goto block_283;
}
}
else
{
lean_del_object(x_295);
lean_dec(x_294);
x_225 = x_284;
x_226 = x_285;
x_227 = x_287;
x_228 = x_288;
x_229 = x_289;
x_230 = x_290;
x_231 = x_291;
x_232 = x_297;
x_233 = x_292;
goto block_283;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_312; 
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec_ref(x_287);
lean_dec(x_285);
lean_dec(x_284);
x_305 = lean_ctor_get(x_293, 0);
x_312 = !lean_is_exclusive(x_293);
if (x_312 == 0)
{
x_306 = x_293;
x_307 = x_312;
goto block_311;
}
else
{
lean_inc(x_305);
lean_dec(x_293);
x_306 = lean_box(0);
x_307 = x_312;
goto block_311;
}
block_311:
{
lean_object* x_308; 
if (x_307 == 0)
{
x_308 = x_306;
goto block_309;
}
else
{
lean_object* x_310; 
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_305);
x_308 = x_310;
goto block_309;
}
block_309:
{
return x_308;
}
}
}
}
block_350:
{
uint8_t x_322; lean_object* x_323; 
x_322 = 0;
lean_inc(x_314);
x_323 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(x_322, x_314, x_319);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; uint8_t x_341; 
x_324 = lean_ctor_get(x_323, 0);
x_341 = !lean_is_exclusive(x_323);
if (x_341 == 0)
{
x_325 = x_323;
x_326 = x_341;
goto block_340;
}
else
{
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_box(0);
x_326 = x_341;
goto block_340;
}
block_340:
{
if (lean_obj_tag(x_324) == 1)
{
if (x_316 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_327 = lean_ctor_get(x_324, 0);
lean_inc(x_327);
lean_dec_ref(x_324);
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_array_get_size(x_315);
x_330 = lean_nat_dec_lt(x_328, x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_327);
lean_dec(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec(x_317);
lean_dec_ref(x_315);
lean_dec(x_314);
x_331 = lean_box(0);
if (x_326 == 0)
{
lean_ctor_set(x_325, 0, x_331);
x_332 = x_325;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_334, 0, x_331);
x_332 = x_334;
goto block_333;
}
block_333:
{
return x_332;
}
}
else
{
lean_del_object(x_325);
x_284 = x_314;
x_285 = x_319;
x_286 = x_316;
x_287 = x_327;
x_288 = x_321;
x_289 = x_320;
x_290 = x_318;
x_291 = x_315;
x_292 = x_317;
goto block_313;
}
}
else
{
lean_object* x_335; 
lean_del_object(x_325);
x_335 = lean_ctor_get(x_324, 0);
lean_inc(x_335);
lean_dec_ref(x_324);
x_284 = x_314;
x_285 = x_319;
x_286 = x_316;
x_287 = x_335;
x_288 = x_321;
x_289 = x_320;
x_290 = x_318;
x_291 = x_315;
x_292 = x_317;
goto block_313;
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_324);
lean_dec(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec(x_317);
lean_dec_ref(x_315);
lean_dec(x_314);
x_336 = lean_box(0);
if (x_326 == 0)
{
lean_ctor_set(x_325, 0, x_336);
x_337 = x_325;
goto block_338;
}
else
{
lean_object* x_339; 
x_339 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_339, 0, x_336);
x_337 = x_339;
goto block_338;
}
block_338:
{
return x_337;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_349; 
lean_dec(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec(x_317);
lean_dec_ref(x_315);
lean_dec(x_314);
x_342 = lean_ctor_get(x_323, 0);
x_349 = !lean_is_exclusive(x_323);
if (x_349 == 0)
{
x_343 = x_323;
x_344 = x_349;
goto block_348;
}
else
{
lean_inc(x_342);
lean_dec(x_323);
x_343 = lean_box(0);
x_344 = x_349;
goto block_348;
}
block_348:
{
lean_object* x_345; 
if (x_344 == 0)
{
x_345 = x_343;
goto block_346;
}
else
{
lean_object* x_347; 
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_342);
x_345 = x_347;
goto block_346;
}
block_346:
{
return x_345;
}
}
}
}
block_367:
{
if (lean_obj_tag(x_351) == 3)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_351, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_351, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_351, 2);
lean_inc_ref(x_362);
lean_dec_ref(x_351);
x_167 = x_360;
x_168 = x_361;
x_169 = x_362;
x_170 = x_352;
x_171 = x_353;
x_172 = x_354;
x_173 = x_355;
x_174 = x_356;
x_175 = x_357;
x_176 = x_358;
x_177 = x_359;
goto block_224;
}
else
{
lean_dec_ref(x_355);
lean_dec_ref(x_353);
if (lean_obj_tag(x_351) == 4)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_351, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 1);
lean_inc_ref(x_364);
lean_dec_ref(x_351);
x_314 = x_363;
x_315 = x_364;
x_316 = x_352;
x_317 = x_354;
x_318 = x_356;
x_319 = x_357;
x_320 = x_358;
x_321 = x_359;
goto block_350;
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_359);
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec(x_351);
x_365 = lean_box(0);
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_365);
return x_366;
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
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
}
#ifdef __cplusplus
}
#endif
