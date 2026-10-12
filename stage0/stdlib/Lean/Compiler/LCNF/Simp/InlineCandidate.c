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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value;
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
static lean_once_cell_t l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_override"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value;
static const lean_array_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`inline` applied to non-local declaration '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`inline` applied to constructor '"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.Simp.InlineCandidate"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Simp.inlineCandidate\?"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 120, .m_data = "assertion violation: ( __do_lift._@.Lean.Compiler.LCNF.Simp.InlineCandidate.450150219._hygCtx._hyg.334.0 ).isSome\n      "};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`inline` applied to parameters is invalid"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 182, 14, 42, 67, 101, 187, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object* v_x_1_){
_start:
{
lean_object* v_params_2_; lean_object* v___x_3_; 
v_params_2_ = lean_ctor_get(v_x_1_, 0);
v___x_3_ = lean_array_get_size(v_params_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_6_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_10_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
lean_ctor_set(v___x_12_, 3, v___x_11_);
lean_ctor_set(v___x_12_, 4, v___x_10_);
lean_ctor_set(v___x_12_, 5, v___x_10_);
lean_ctor_set(v___x_12_, 6, v___x_10_);
lean_ctor_set(v___x_12_, 7, v___x_10_);
lean_ctor_set(v___x_12_, 8, v___x_10_);
lean_ctor_set(v___x_12_, 9, v___x_10_);
lean_ctor_set(v___x_12_, 10, v___x_10_);
lean_ctor_set(v___x_12_, 11, v___x_9_);
return v___x_12_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(lean_object* v_msg_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_ref_19_; lean_object* v___x_20_; lean_object* v_env_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_ref_19_ = lean_ctor_get(v___y_16_, 2);
v___x_20_ = lean_st_ref_get(v___y_17_);
v_env_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc_ref(v_env_21_);
lean_dec(v___x_20_);
v___x_22_ = lean_st_ref_get(v___y_15_);
v___x_23_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_14_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_46_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_46_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_46_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_46_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v_lctx_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_44_; 
v_lctx_28_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v___x_22_, 1);
lean_dec(v_unused_45_);
v___x_30_ = v___x_22_;
v_isShared_31_ = v_isSharedCheck_44_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_lctx_28_);
lean_dec(v___x_22_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_44_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_32_ = lean_unbox(v_a_24_);
lean_dec(v_a_24_);
v___x_33_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_28_, v___x_32_);
lean_dec_ref(v_lctx_28_);
v___x_34_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_16_);
v___x_35_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v_env_21_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
lean_ctor_set(v___x_36_, 2, v___x_33_);
lean_ctor_set(v___x_36_, 3, v___x_34_);
if (v_isShared_31_ == 0)
{
lean_ctor_set_tag(v___x_30_, 3);
lean_ctor_set(v___x_30_, 1, v_msg_13_);
lean_ctor_set(v___x_30_, 0, v___x_36_);
v___x_38_ = v___x_30_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_msg_13_);
v___x_38_ = v_reuseFailAlloc_43_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_19_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_19_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
if (v_isShared_27_ == 0)
{
lean_ctor_set_tag(v___x_26_, 1);
lean_ctor_set(v___x_26_, 0, v___x_39_);
v___x_41_ = v___x_26_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
else
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
lean_dec(v___x_22_);
lean_dec_ref(v_env_21_);
lean_dec_ref(v_msg_13_);
v_a_47_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___x_23_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_23_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_13_ = stack[0].m_obj;
lean_object* v___y_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v_msg_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___boxed(lean_object* v_msg_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v_msg_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_62_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_object* v_00_u03b1_63_, lean_object* v_msg_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v_msg_64_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_64_ = stack[1].m_obj;
lean_object* v___y_65_ = stack[2].m_obj;
lean_object* v___y_66_ = stack[3].m_obj;
lean_object* v___y_67_ = stack[4].m_obj;
lean_object* v___y_68_ = stack[5].m_obj;
lean_object* v___y_69_ = stack[6].m_obj;
lean_object* v___y_70_ = stack[7].m_obj;
lean_object* v___y_71_ = stack[8].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(lean_box(0), v_msg_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(lean_object* v_00_u03b1_75_, lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(v_00_u03b1_75_, v_msg_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_85_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_instMonadEIO___redArg();
return v___x_86_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(lean_object* v_msg_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_toApplicative_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_166_; 
v___x_100_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
v___x_101_ = l_StateRefT_x27_instMonad___redArg(v___x_100_);
v_toApplicative_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v___x_101_, 1);
lean_dec(v_unused_167_);
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_166_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_toApplicative_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_166_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_toFunctor_106_; lean_object* v_toSeq_107_; lean_object* v_toSeqLeft_108_; lean_object* v_toSeqRight_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_164_; 
v_toFunctor_106_ = lean_ctor_get(v_toApplicative_102_, 0);
v_toSeq_107_ = lean_ctor_get(v_toApplicative_102_, 2);
v_toSeqLeft_108_ = lean_ctor_get(v_toApplicative_102_, 3);
v_toSeqRight_109_ = lean_ctor_get(v_toApplicative_102_, 4);
v_isSharedCheck_164_ = !lean_is_exclusive(v_toApplicative_102_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_toApplicative_102_, 1);
lean_dec(v_unused_165_);
v___x_111_ = v_toApplicative_102_;
v_isShared_112_ = v_isSharedCheck_164_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_toSeqRight_109_);
lean_inc(v_toSeqLeft_108_);
lean_inc(v_toSeq_107_);
lean_inc(v_toFunctor_106_);
lean_dec(v_toApplicative_102_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_164_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___x_122_; 
v___f_113_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1));
v___f_114_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2));
lean_inc_ref(v_toFunctor_106_);
v___f_115_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_115_, 0, v_toFunctor_106_);
v___f_116_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_116_, 0, v_toFunctor_106_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___f_115_);
lean_ctor_set(v___x_117_, 1, v___f_116_);
v___f_118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_118_, 0, v_toSeqRight_109_);
v___f_119_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_119_, 0, v_toSeqLeft_108_);
v___f_120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_120_, 0, v_toSeq_107_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v___f_118_);
lean_ctor_set(v___x_111_, 3, v___f_119_);
lean_ctor_set(v___x_111_, 2, v___f_120_);
lean_ctor_set(v___x_111_, 1, v___f_113_);
lean_ctor_set(v___x_111_, 0, v___x_117_);
v___x_122_ = v___x_111_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___f_113_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v___f_120_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v___f_119_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v___f_118_);
v___x_122_ = v_reuseFailAlloc_163_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_124_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___f_114_);
lean_ctor_set(v___x_104_, 0, v___x_122_);
v___x_124_ = v___x_104_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___f_114_);
v___x_124_ = v_reuseFailAlloc_162_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v_toApplicative_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_160_; 
v___x_125_ = l_StateRefT_x27_instMonad___redArg(v___x_124_);
v_toApplicative_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_125_, 1);
lean_dec(v_unused_161_);
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_160_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_toApplicative_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_160_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_toFunctor_130_; lean_object* v_toSeq_131_; lean_object* v_toSeqLeft_132_; lean_object* v_toSeqRight_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_158_; 
v_toFunctor_130_ = lean_ctor_get(v_toApplicative_126_, 0);
v_toSeq_131_ = lean_ctor_get(v_toApplicative_126_, 2);
v_toSeqLeft_132_ = lean_ctor_get(v_toApplicative_126_, 3);
v_toSeqRight_133_ = lean_ctor_get(v_toApplicative_126_, 4);
v_isSharedCheck_158_ = !lean_is_exclusive(v_toApplicative_126_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_toApplicative_126_, 1);
lean_dec(v_unused_159_);
v___x_135_ = v_toApplicative_126_;
v_isShared_136_ = v_isSharedCheck_158_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_toSeqRight_133_);
lean_inc(v_toSeqLeft_132_);
lean_inc(v_toSeq_131_);
lean_inc(v_toFunctor_130_);
lean_dec(v_toApplicative_126_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_158_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_146_; 
v___f_137_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3));
v___f_138_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4));
lean_inc_ref(v_toFunctor_130_);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_139_, 0, v_toFunctor_130_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toFunctor_130_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___f_139_);
lean_ctor_set(v___x_141_, 1, v___f_140_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeqRight_133_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_143_, 0, v_toSeqLeft_132_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeq_131_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 4, v___f_142_);
lean_ctor_set(v___x_135_, 3, v___f_143_);
lean_ctor_set(v___x_135_, 2, v___f_144_);
lean_ctor_set(v___x_135_, 1, v___f_137_);
lean_ctor_set(v___x_135_, 0, v___x_141_);
v___x_146_ = v___x_135_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v___f_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v___f_143_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v___f_142_);
v___x_146_ = v_reuseFailAlloc_157_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___f_138_);
lean_ctor_set(v___x_128_, 0, v___x_146_);
v___x_148_ = v___x_128_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___f_138_);
v___x_148_ = v_reuseFailAlloc_156_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___f_153_; lean_object* v___x_16148__overap_154_; lean_object* v___x_155_; 
v___x_149_ = l_ReaderT_instMonad___redArg(v___x_148_);
v___x_150_ = l_StateRefT_x27_instMonad___redArg(v___x_149_);
v___x_151_ = lean_box(0);
v___x_152_ = l_instInhabitedOfMonad___redArg(v___x_150_, v___x_151_);
v___f_153_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_153_, 0, v___x_152_);
v___x_16148__overap_154_ = lean_panic_fn_borrowed(v___f_153_, v_msg_91_);
lean_dec_ref(v___f_153_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
lean_inc(v___y_96_);
lean_inc_ref(v___y_95_);
lean_inc_ref(v___y_94_);
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
v___x_155_ = lean_apply_8(v___x_16148__overap_154_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, lean_box(0));
return v___x_155_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_91_ = stack[0].m_obj;
lean_object* v___y_92_ = stack[1].m_obj;
lean_object* v___y_93_ = stack[2].m_obj;
lean_object* v___y_94_ = stack[3].m_obj;
lean_object* v___y_95_ = stack[4].m_obj;
lean_object* v___y_96_ = stack[5].m_obj;
lean_object* v___y_97_ = stack[6].m_obj;
lean_object* v___y_98_ = stack[7].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(v_msg_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(lean_object* v_msg_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(v_msg_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_178_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object* v_val_179_, uint8_t v___x_180_, lean_object* v_code_181_, uint8_t v_mustInline_182_, uint8_t v_inlineDefs_183_, lean_object* v_____r_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(v_val_179_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(v_val_179_);
if (v___x_194_ == 0)
{
if (v___x_180_ == 0)
{
uint8_t v___x_195_; 
v___x_195_ = l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(v_val_179_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_181_, v___y_188_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(v_mustInline_182_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(v_inlineDefs_183_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_box(v_inlineDefs_183_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_box(v_inlineDefs_183_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_179_ = stack[0].m_obj;
uint8_t v___x_180_ = stack[1].m_num;
lean_object* v_code_181_ = stack[2].m_obj;
uint8_t v_mustInline_182_ = stack[3].m_num;
uint8_t v_inlineDefs_183_ = stack[4].m_num;
lean_object* v_____r_184_ = stack[5].m_obj;
lean_object* v___y_185_ = stack[6].m_obj;
lean_object* v___y_186_ = stack[7].m_obj;
lean_object* v___y_187_ = stack[8].m_obj;
lean_object* v___y_188_ = stack[9].m_obj;
lean_object* v___y_189_ = stack[10].m_obj;
lean_object* v___y_190_ = stack[11].m_obj;
lean_object* v___y_191_ = stack[12].m_obj;
lean_object* v_res_205_;
v_res_205_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(v_val_179_, v___x_180_, v_code_181_, v_mustInline_182_, v_inlineDefs_183_, v_____r_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object* v_val_206_, lean_object* v___x_207_, lean_object* v_code_208_, lean_object* v_mustInline_209_, lean_object* v_inlineDefs_210_, lean_object* v_____r_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v___x_16951__boxed_220_; uint8_t v_mustInline_boxed_221_; uint8_t v_inlineDefs_boxed_222_; lean_object* v_res_223_; 
v___x_16951__boxed_220_ = lean_unbox(v___x_207_);
v_mustInline_boxed_221_ = lean_unbox(v_mustInline_209_);
v_inlineDefs_boxed_222_ = lean_unbox(v_inlineDefs_210_);
v_res_223_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(v_val_206_, v___x_16951__boxed_220_, v_code_208_, v_mustInline_boxed_221_, v_inlineDefs_boxed_222_, v_____r_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v_code_208_);
lean_dec_ref(v_val_206_);
return v_res_223_;
}
}
lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_toApplicative_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_329_; 
v___x_235_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
v___x_236_ = l_StateRefT_x27_instMonad___redArg(v___x_235_);
v_toApplicative_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_236_, 1);
lean_dec(v_unused_330_);
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_329_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_toApplicative_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_329_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_toFunctor_241_; lean_object* v_toSeq_242_; lean_object* v_toSeqLeft_243_; lean_object* v_toSeqRight_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_327_; 
v_toFunctor_241_ = lean_ctor_get(v_toApplicative_237_, 0);
v_toSeq_242_ = lean_ctor_get(v_toApplicative_237_, 2);
v_toSeqLeft_243_ = lean_ctor_get(v_toApplicative_237_, 3);
v_toSeqRight_244_ = lean_ctor_get(v_toApplicative_237_, 4);
v_isSharedCheck_327_ = !lean_is_exclusive(v_toApplicative_237_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_toApplicative_237_, 1);
lean_dec(v_unused_328_);
v___x_246_ = v_toApplicative_237_;
v_isShared_247_ = v_isSharedCheck_327_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_toSeqRight_244_);
lean_inc(v_toSeqLeft_243_);
lean_inc(v_toSeq_242_);
lean_inc(v_toFunctor_241_);
lean_dec(v_toApplicative_237_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_327_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___x_257_; 
v___f_248_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1));
v___f_249_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2));
lean_inc_ref(v_toFunctor_241_);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_250_, 0, v_toFunctor_241_);
v___f_251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_251_, 0, v_toFunctor_241_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___f_250_);
lean_ctor_set(v___x_252_, 1, v___f_251_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_253_, 0, v_toSeqRight_244_);
v___f_254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_254_, 0, v_toSeqLeft_243_);
v___f_255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_255_, 0, v_toSeq_242_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 4, v___f_253_);
lean_ctor_set(v___x_246_, 3, v___f_254_);
lean_ctor_set(v___x_246_, 2, v___f_255_);
lean_ctor_set(v___x_246_, 1, v___f_248_);
lean_ctor_set(v___x_246_, 0, v___x_252_);
v___x_257_ = v___x_246_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___f_248_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v___f_255_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v___f_254_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v___f_253_);
v___x_257_ = v_reuseFailAlloc_326_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___f_249_);
lean_ctor_set(v___x_239_, 0, v___x_257_);
v___x_259_ = v___x_239_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___f_249_);
v___x_259_ = v_reuseFailAlloc_325_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v_toApplicative_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_323_; 
v___x_260_ = l_StateRefT_x27_instMonad___redArg(v___x_259_);
v_toApplicative_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v___x_260_, 1);
lean_dec(v_unused_324_);
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_323_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_toApplicative_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_323_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_toFunctor_265_; lean_object* v_toSeq_266_; lean_object* v_toSeqLeft_267_; lean_object* v_toSeqRight_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_321_; 
v_toFunctor_265_ = lean_ctor_get(v_toApplicative_261_, 0);
v_toSeq_266_ = lean_ctor_get(v_toApplicative_261_, 2);
v_toSeqLeft_267_ = lean_ctor_get(v_toApplicative_261_, 3);
v_toSeqRight_268_ = lean_ctor_get(v_toApplicative_261_, 4);
v_isSharedCheck_321_ = !lean_is_exclusive(v_toApplicative_261_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_toApplicative_261_, 1);
lean_dec(v_unused_322_);
v___x_270_ = v_toApplicative_261_;
v_isShared_271_ = v_isSharedCheck_321_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_toSeqRight_268_);
lean_inc(v_toSeqLeft_267_);
lean_inc(v_toSeq_266_);
lean_inc(v_toFunctor_265_);
lean_dec(v_toApplicative_261_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_321_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___x_281_; 
v___f_272_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3));
v___f_273_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4));
lean_inc_ref(v_toFunctor_265_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_274_, 0, v_toFunctor_265_);
v___f_275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_275_, 0, v_toFunctor_265_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___f_274_);
lean_ctor_set(v___x_276_, 1, v___f_275_);
v___f_277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_277_, 0, v_toSeqRight_268_);
v___f_278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_278_, 0, v_toSeqLeft_267_);
v___f_279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_279_, 0, v_toSeq_266_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v___f_277_);
lean_ctor_set(v___x_270_, 3, v___f_278_);
lean_ctor_set(v___x_270_, 2, v___f_279_);
lean_ctor_set(v___x_270_, 1, v___f_272_);
lean_ctor_set(v___x_270_, 0, v___x_276_);
v___x_281_ = v___x_270_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___f_272_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v___f_279_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v___f_278_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v___f_277_);
v___x_281_ = v_reuseFailAlloc_320_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_283_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___f_273_);
lean_ctor_set(v___x_263_, 0, v___x_281_);
v___x_283_ = v___x_263_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___f_273_);
v___x_283_ = v_reuseFailAlloc_319_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_toApplicative_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_317_; 
v___x_284_ = l_ReaderT_instMonad___redArg(v___x_283_);
v___x_285_ = l_StateRefT_x27_instMonad___redArg(v___x_284_);
v_toApplicative_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_285_, 1);
lean_dec(v_unused_318_);
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_317_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_toApplicative_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_317_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_toFunctor_290_; lean_object* v_toSeq_291_; lean_object* v_toSeqLeft_292_; lean_object* v_toSeqRight_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_315_; 
v_toFunctor_290_ = lean_ctor_get(v_toApplicative_286_, 0);
v_toSeq_291_ = lean_ctor_get(v_toApplicative_286_, 2);
v_toSeqLeft_292_ = lean_ctor_get(v_toApplicative_286_, 3);
v_toSeqRight_293_ = lean_ctor_get(v_toApplicative_286_, 4);
v_isSharedCheck_315_ = !lean_is_exclusive(v_toApplicative_286_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v_toApplicative_286_, 1);
lean_dec(v_unused_316_);
v___x_295_ = v_toApplicative_286_;
v_isShared_296_ = v_isSharedCheck_315_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_toSeqRight_293_);
lean_inc(v_toSeqLeft_292_);
lean_inc(v_toSeq_291_);
lean_inc(v_toFunctor_290_);
lean_dec(v_toApplicative_286_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_315_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___x_306_; 
v___f_297_ = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0));
v___f_298_ = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1));
lean_inc_ref(v_toFunctor_290_);
v___f_299_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_299_, 0, v_toFunctor_290_);
v___f_300_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_300_, 0, v_toFunctor_290_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___f_299_);
lean_ctor_set(v___x_301_, 1, v___f_300_);
v___f_302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_302_, 0, v_toSeqRight_293_);
v___f_303_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_303_, 0, v_toSeqLeft_292_);
v___f_304_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_304_, 0, v_toSeq_291_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 4, v___f_302_);
lean_ctor_set(v___x_295_, 3, v___f_303_);
lean_ctor_set(v___x_295_, 2, v___f_304_);
lean_ctor_set(v___x_295_, 1, v___f_297_);
lean_ctor_set(v___x_295_, 0, v___x_301_);
v___x_306_ = v___x_295_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___f_297_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v___f_304_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v___f_303_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v___f_302_);
v___x_306_ = v_reuseFailAlloc_314_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___f_298_);
lean_ctor_set(v___x_288_, 0, v___x_306_);
v___x_308_ = v___x_288_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___f_298_);
v___x_308_ = v_reuseFailAlloc_313_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_16169__overap_311_; lean_object* v___x_312_; 
v___x_309_ = lean_box(0);
v___x_310_ = l_instInhabitedOfMonad___redArg(v___x_308_, v___x_309_);
v___x_16169__overap_311_ = lean_panic_fn_borrowed(v___x_310_, v_msg_226_);
lean_dec(v___x_310_);
lean_inc(v___y_233_);
lean_inc_ref(v___y_232_);
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
v___x_312_ = lean_apply_8(v___x_16169__overap_311_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, lean_box(0));
return v___x_312_;
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
LEAN_EXPORT void l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_226_ = stack[0].m_obj;
lean_object* v___y_227_ = stack[1].m_obj;
lean_object* v___y_228_ = stack[2].m_obj;
lean_object* v___y_229_ = stack[3].m_obj;
lean_object* v___y_230_ = stack[4].m_obj;
lean_object* v___y_231_ = stack[5].m_obj;
lean_object* v___y_232_ = stack[6].m_obj;
lean_object* v___y_233_ = stack[7].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v_msg_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v_msg_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_345_ = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2));
v___x_346_ = lean_unsigned_to_nat(11u);
v___x_347_ = lean_unsigned_to_nat(122u);
v___x_348_ = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1));
v___x_349_ = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0));
v___x_350_ = l_mkPanicMessageWithDecl(v___x_349_, v___x_348_, v___x_347_, v___x_346_, v___x_345_);
return v___x_350_;
}
}
lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(lean_object* v_constName_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v_env_364_; uint8_t v___x_365_; lean_object* v___x_366_; 
v___x_360_ = lean_st_ref_get(v___y_358_);
v_env_364_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_360_);
v___x_365_ = 0;
v___x_366_ = l_Lean_Environment_findAsync_x3f(v_env_364_, v_constName_351_, v___x_365_);
if (lean_obj_tag(v___x_366_) == 1)
{
lean_object* v_val_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_386_; 
v_val_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_386_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_386_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_val_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_386_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v_kind_371_; 
v_kind_371_ = lean_ctor_get_uint8(v_val_367_, sizeof(void*)*3);
if (v_kind_371_ == 6)
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_367_);
if (lean_obj_tag(v___x_372_) == 6)
{
lean_object* v_val_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_383_; 
v_val_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_383_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_val_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v_val_373_);
v___x_378_ = v___x_369_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_val_373_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 0);
lean_ctor_set(v___x_375_, 0, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v___x_372_);
lean_del_object(v___x_369_);
v___x_384_ = lean_obj_once(&l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3, &l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once, _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3);
v___x_385_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v___x_384_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
return v___x_385_;
}
}
else
{
lean_del_object(v___x_369_);
lean_dec(v_val_367_);
goto v___jp_361_;
}
}
}
else
{
lean_dec(v___x_366_);
goto v___jp_361_;
}
v___jp_361_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT void l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_351_ = stack[0].m_obj;
lean_object* v___y_352_ = stack[1].m_obj;
lean_object* v___y_353_ = stack[2].m_obj;
lean_object* v___y_354_ = stack[3].m_obj;
lean_object* v___y_355_ = stack[4].m_obj;
lean_object* v___y_356_ = stack[5].m_obj;
lean_object* v___y_357_ = stack[6].m_obj;
lean_object* v___y_358_ = stack[7].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(v_constName_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(lean_object* v_constName_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(v_constName_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3));
v___x_404_ = l_Lean_stringToMessageData(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_414_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11));
v___x_415_ = lean_unsigned_to_nat(6u);
v___x_416_ = lean_unsigned_to_nat(54u);
v___x_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10));
v___x_418_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9));
v___x_419_ = l_mkPanicMessageWithDecl(v___x_418_, v___x_417_, v___x_416_, v___x_415_, v___x_414_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object* v_e_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
uint8_t v_mustInline_438_; uint8_t v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; uint8_t v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; uint8_t v___y_477_; lean_object* v___y_478_; uint8_t v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; uint8_t v___y_526_; lean_object* v___y_527_; uint8_t v___y_528_; lean_object* v___y_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; uint8_t v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; uint8_t v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; uint8_t v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; uint8_t v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___y_587_; lean_object* v___y_588_; uint8_t v___y_589_; uint8_t v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v_declName_611_; lean_object* v_us_612_; lean_object* v_args_613_; uint8_t v_mustInline_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_730_; lean_object* v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v_fvarId_760_; lean_object* v_args_761_; uint8_t v_mustInline_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v_e_797_; uint8_t v_mustInline_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; 
v_mustInline_438_ = 0;
if (lean_obj_tag(v_e_423_) == 3)
{
lean_object* v_declName_813_; 
v_declName_813_ = lean_ctor_get(v_e_423_, 0);
lean_inc(v_declName_813_);
if (lean_obj_tag(v_declName_813_) == 1)
{
lean_object* v_pre_814_; 
v_pre_814_ = lean_ctor_get(v_declName_813_, 0);
if (lean_obj_tag(v_pre_814_) == 0)
{
lean_object* v_us_815_; lean_object* v_args_816_; lean_object* v_str_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_us_815_ = lean_ctor_get(v_e_423_, 1);
lean_inc(v_us_815_);
v_args_816_ = lean_ctor_get(v_e_423_, 2);
lean_inc_ref(v_args_816_);
lean_dec_ref_known(v_e_423_, 3);
v_str_817_ = lean_ctor_get(v_declName_813_, 1);
v___x_818_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1));
v___x_819_ = lean_string_dec_eq(v_str_817_, v___x_818_);
if (v___x_819_ == 0)
{
v_declName_611_ = v_declName_813_;
v_us_612_ = v_us_815_;
v_args_613_ = v_args_816_;
v_mustInline_614_ = v_mustInline_438_;
v___y_615_ = v_a_424_;
v___y_616_ = v_a_425_;
v___y_617_ = v_a_426_;
v___y_618_ = v_a_427_;
v___y_619_ = v_a_428_;
v___y_620_ = v_a_429_;
v___y_621_ = v_a_430_;
goto v___jp_610_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v_mustInline_822_; 
v___x_820_ = lean_array_get_size(v_args_816_);
v___x_821_ = lean_unsigned_to_nat(2u);
v_mustInline_822_ = lean_nat_dec_eq(v___x_820_, v___x_821_);
if (v_mustInline_822_ == 0)
{
v_declName_611_ = v_declName_813_;
v_us_612_ = v_us_815_;
v_args_613_ = v_args_816_;
v_mustInline_614_ = v_mustInline_438_;
v___y_615_ = v_a_424_;
v___y_616_ = v_a_425_;
v___y_617_ = v_a_426_;
v___y_618_ = v_a_427_;
v___y_619_ = v_a_428_;
v___y_620_ = v_a_429_;
v___y_621_ = v_a_430_;
goto v___jp_610_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_array_fget_borrowed(v_args_816_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 1)
{
lean_object* v_fvarId_825_; uint8_t v___x_826_; lean_object* v___x_827_; 
lean_inc_ref(v___x_824_);
lean_dec_ref(v_args_816_);
lean_dec(v_us_815_);
lean_dec_ref_known(v_declName_813_, 2);
v_fvarId_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc_n(v_fvarId_825_, 2);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = 0;
v___x_827_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_826_, v_fvarId_825_, v_a_428_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
if (lean_obj_tag(v_a_828_) == 1)
{
lean_object* v_val_829_; lean_object* v_fvarId_830_; lean_object* v___x_831_; 
lean_dec(v_fvarId_825_);
v_val_829_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_a_828_, 1);
v_fvarId_830_ = lean_ctor_get(v_val_829_, 0);
lean_inc(v_fvarId_830_);
lean_dec(v_val_829_);
v___x_831_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2));
v_fvarId_760_ = v_fvarId_830_;
v_args_761_ = v___x_831_;
v_mustInline_762_ = v_mustInline_822_;
v___y_763_ = v_a_425_;
v___y_764_ = v_a_427_;
v___y_765_ = v_a_428_;
v___y_766_ = v_a_429_;
v___y_767_ = v_a_430_;
goto v___jp_759_;
}
else
{
lean_object* v___x_832_; 
lean_dec(v_a_828_);
v___x_832_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_826_, v_fvarId_825_, v_a_428_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
if (lean_obj_tag(v_a_833_) == 1)
{
lean_object* v_val_834_; lean_object* v_value_835_; 
lean_dec(v_fvarId_825_);
v_val_834_ = lean_ctor_get(v_a_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v_a_833_, 1);
v_value_835_ = lean_ctor_get(v_val_834_, 3);
lean_inc(v_value_835_);
lean_dec(v_val_834_);
if (lean_obj_tag(v_value_835_) == 3)
{
lean_object* v_declName_836_; lean_object* v_us_837_; lean_object* v_args_838_; lean_object* v___x_839_; 
v_declName_836_ = lean_ctor_get(v_value_835_, 0);
lean_inc_n(v_declName_836_, 2);
v_us_837_ = lean_ctor_get(v_value_835_, 1);
lean_inc(v_us_837_);
v_args_838_ = lean_ctor_get(v_value_835_, 2);
lean_inc_ref(v_args_838_);
lean_dec_ref_known(v_value_835_, 3);
v___x_839_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(v_declName_836_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
if (lean_obj_tag(v_a_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_427_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; uint8_t v___x_843_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v___x_843_ = lean_unbox(v_a_842_);
lean_dec(v_a_842_);
v___x_844_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_836_, v___x_843_, v_a_430_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
if (lean_obj_tag(v_a_845_) == 1)
{
lean_dec_ref_known(v_a_845_, 1);
v_declName_611_ = v_declName_836_;
v_us_612_ = v_us_837_;
v_args_613_ = v_args_838_;
v_mustInline_614_ = v_mustInline_822_;
v___y_615_ = v_a_424_;
v___y_616_ = v_a_425_;
v___y_617_ = v_a_426_;
v___y_618_ = v_a_427_;
v___y_619_ = v_a_428_;
v___y_620_ = v_a_429_;
v___y_621_ = v_a_430_;
goto v___jp_610_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_a_845_);
lean_dec_ref(v_args_838_);
lean_dec(v_us_837_);
v___x_846_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4);
v___x_847_ = l_Lean_MessageData_ofName(v_declName_836_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_850_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v_args_838_);
lean_dec(v_us_837_);
lean_dec(v_declName_836_);
v_a_860_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_844_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_844_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v_args_838_);
lean_dec(v_us_837_);
lean_dec(v_declName_836_);
v_a_868_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_841_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_841_);
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
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref_known(v_a_840_, 1);
lean_dec_ref(v_args_838_);
lean_dec(v_us_837_);
v___x_876_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8);
v___x_877_ = l_Lean_MessageData_ofName(v_declName_836_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_880_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_args_838_);
lean_dec(v_us_837_);
lean_dec(v_declName_836_);
v_a_890_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_839_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_839_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
v_e_797_ = v_value_835_;
v_mustInline_798_ = v_mustInline_822_;
v___y_799_ = v_a_424_;
v___y_800_ = v_a_425_;
v___y_801_ = v_a_426_;
v___y_802_ = v_a_427_;
v___y_803_ = v_a_428_;
v___y_804_ = v_a_429_;
v___y_805_ = v_a_430_;
goto v___jp_796_;
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v_a_833_);
v___x_898_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v___x_826_, v_fvarId_825_, v_a_428_);
lean_dec(v_fvarId_825_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
if (lean_obj_tag(v_a_899_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12);
v___x_901_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(v___x_900_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref_known(v_a_899_, 1);
v___x_902_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14, &l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_once, _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14);
v___x_903_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_902_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_912_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_898_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_898_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_fvarId_825_);
v_a_920_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_832_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_832_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_fvarId_825_);
v_a_928_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_827_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_827_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
v_declName_611_ = v_declName_813_;
v_us_612_ = v_us_815_;
v_args_613_ = v_args_816_;
v_mustInline_614_ = v_mustInline_438_;
v___y_615_ = v_a_424_;
v___y_616_ = v_a_425_;
v___y_617_ = v_a_426_;
v___y_618_ = v_a_427_;
v___y_619_ = v_a_428_;
v___y_620_ = v_a_429_;
v___y_621_ = v_a_430_;
goto v___jp_610_;
}
}
}
}
else
{
lean_object* v_us_936_; lean_object* v_args_937_; 
v_us_936_ = lean_ctor_get(v_e_423_, 1);
lean_inc(v_us_936_);
v_args_937_ = lean_ctor_get(v_e_423_, 2);
lean_inc_ref(v_args_937_);
lean_dec_ref_known(v_e_423_, 3);
v_declName_611_ = v_declName_813_;
v_us_612_ = v_us_936_;
v_args_613_ = v_args_937_;
v_mustInline_614_ = v_mustInline_438_;
v___y_615_ = v_a_424_;
v___y_616_ = v_a_425_;
v___y_617_ = v_a_426_;
v___y_618_ = v_a_427_;
v___y_619_ = v_a_428_;
v___y_620_ = v_a_429_;
v___y_621_ = v_a_430_;
goto v___jp_610_;
}
}
else
{
lean_object* v_us_938_; lean_object* v_args_939_; 
v_us_938_ = lean_ctor_get(v_e_423_, 1);
lean_inc(v_us_938_);
v_args_939_ = lean_ctor_get(v_e_423_, 2);
lean_inc_ref(v_args_939_);
lean_dec_ref_known(v_e_423_, 3);
v_declName_611_ = v_declName_813_;
v_us_612_ = v_us_938_;
v_args_613_ = v_args_939_;
v_mustInline_614_ = v_mustInline_438_;
v___y_615_ = v_a_424_;
v___y_616_ = v_a_425_;
v___y_617_ = v_a_426_;
v___y_618_ = v_a_427_;
v___y_619_ = v_a_428_;
v___y_620_ = v_a_429_;
v___y_621_ = v_a_430_;
goto v___jp_610_;
}
}
else
{
v_e_797_ = v_e_423_;
v_mustInline_798_ = v_mustInline_438_;
v___y_799_ = v_a_424_;
v___y_800_ = v_a_425_;
v___y_801_ = v_a_426_;
v___y_802_ = v_a_427_;
v___y_803_ = v_a_428_;
v___y_804_ = v_a_429_;
v___y_805_ = v_a_430_;
goto v___jp_796_;
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
v___jp_435_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
v___jp_439_:
{
lean_object* v_levelParams_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_levelParams_449_ = lean_ctor_get(v___y_445_, 1);
lean_inc(v_levelParams_449_);
lean_dec_ref(v___y_445_);
lean_inc_n(v___y_444_, 2);
lean_inc_ref(v___y_441_);
v___x_450_ = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(v___y_443_, v___y_441_, v___y_444_);
v___x_451_ = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(v___y_447_, v_levelParams_449_, v___y_444_);
v___x_452_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(v___y_441_, v___y_444_);
v___x_453_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v___y_448_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_462_; 
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_453_, 0);
lean_dec(v_unused_463_);
v___x_455_ = v___x_453_;
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
else
{
lean_dec(v___x_453_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(v___x_457_, 0, v___x_450_);
lean_ctor_set(v___x_457_, 1, v___x_451_);
lean_ctor_set(v___x_457_, 2, v___x_452_);
lean_ctor_set(v___x_457_, 3, v___y_442_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*4, v_mustInline_438_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*4 + 1, v___y_446_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*4 + 2, v___y_440_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v___x_452_);
lean_dec_ref(v___x_451_);
lean_dec_ref(v___x_450_);
lean_dec_ref(v___y_442_);
v_a_464_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_453_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_453_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
v___jp_472_:
{
if (v___y_477_ == 0)
{
v___y_440_ = v___y_479_;
v___y_441_ = v___y_474_;
v___y_442_ = v___y_480_;
v___y_443_ = v___y_481_;
v___y_444_ = v___y_483_;
v___y_445_ = v___y_476_;
v___y_446_ = v___y_477_;
v___y_447_ = v___y_478_;
v___y_448_ = v___y_482_;
goto v___jp_439_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(v___y_474_);
if (lean_obj_tag(v___x_485_) == 1)
{
lean_object* v_val_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_516_; 
v_val_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_516_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_val_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v___y_480_);
v___x_491_ = lean_nat_dec_lt(v_val_486_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_val_486_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___y_474_);
v___x_492_ = lean_box(0);
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 0);
lean_ctor_set(v___x_488_, 0, v___x_492_);
v___x_494_ = v___x_488_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_del_object(v___x_488_);
v___x_496_ = lean_array_get_borrowed(v___y_475_, v___y_480_, v_val_486_);
lean_dec(v_val_486_);
v___x_497_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v___x_496_, v___y_484_, v___y_473_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_507_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; 
v___x_502_ = lean_unbox(v_a_498_);
lean_dec(v_a_498_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v___y_483_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___y_474_);
v___x_503_ = lean_box(0);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_del_object(v___x_500_);
v___y_440_ = v___y_479_;
v___y_441_ = v___y_474_;
v___y_442_ = v___y_480_;
v___y_443_ = v___y_481_;
v___y_444_ = v___y_483_;
v___y_445_ = v___y_476_;
v___y_446_ = v___y_477_;
v___y_447_ = v___y_478_;
v___y_448_ = v___y_482_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v___y_483_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___y_474_);
v_a_508_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_497_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_497_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_485_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___y_474_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
v___jp_519_:
{
if (lean_obj_tag(v___y_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_547_; 
v_a_535_ = lean_ctor_get(v___y_534_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___y_534_);
if (v_isSharedCheck_547_ == 0)
{
v___x_537_ = v___y_534_;
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___y_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = lean_unbox(v_a_535_);
lean_dec(v_a_535_);
if (v___x_539_ == 0)
{
lean_del_object(v___x_537_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_522_);
goto v___jp_435_;
}
else
{
if (v___y_525_ == 0)
{
if (v___y_520_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v___y_522_);
v___x_541_ = lean_array_get_size(v___y_529_);
v___x_542_ = lean_nat_dec_lt(v___x_541_, v___x_540_);
lean_dec(v___x_540_);
if (v___x_542_ == 0)
{
lean_del_object(v___x_537_);
v___y_473_ = v___y_521_;
v___y_474_ = v___y_522_;
v___y_475_ = v___y_523_;
v___y_476_ = v___y_524_;
v___y_477_ = v___y_526_;
v___y_478_ = v___y_527_;
v___y_479_ = v___y_528_;
v___y_480_ = v___y_529_;
v___y_481_ = v___y_530_;
v___y_482_ = v___y_531_;
v___y_483_ = v___y_532_;
v___y_484_ = v___y_533_;
goto v___jp_472_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_545_; 
lean_dec(v___y_532_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_522_);
v___x_543_ = lean_box(0);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_543_);
v___x_545_ = v___x_537_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_del_object(v___x_537_);
v___y_473_ = v___y_521_;
v___y_474_ = v___y_522_;
v___y_475_ = v___y_523_;
v___y_476_ = v___y_524_;
v___y_477_ = v___y_526_;
v___y_478_ = v___y_527_;
v___y_479_ = v___y_528_;
v___y_480_ = v___y_529_;
v___y_481_ = v___y_530_;
v___y_482_ = v___y_531_;
v___y_483_ = v___y_532_;
v___y_484_ = v___y_533_;
goto v___jp_472_;
}
}
else
{
lean_del_object(v___x_537_);
v___y_473_ = v___y_521_;
v___y_474_ = v___y_522_;
v___y_475_ = v___y_523_;
v___y_476_ = v___y_524_;
v___y_477_ = v___y_526_;
v___y_478_ = v___y_527_;
v___y_479_ = v___y_528_;
v___y_480_ = v___y_529_;
v___y_481_ = v___y_530_;
v___y_482_ = v___y_531_;
v___y_483_ = v___y_532_;
v___y_484_ = v___y_533_;
goto v___jp_472_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v___y_532_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_522_);
v_a_548_ = lean_ctor_get(v___y_534_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___y_534_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___y_534_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___y_534_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
v___jp_556_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(0);
lean_inc(v___y_558_);
lean_inc_ref(v___y_563_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_570_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_573_);
lean_inc_ref(v___y_575_);
v___x_577_ = lean_apply_9(v___y_566_, v___x_576_, v___y_575_, v___y_573_, v___y_571_, v___y_570_, v___y_574_, v___y_563_, v___y_558_, lean_box(0));
v___y_520_ = v___y_557_;
v___y_521_ = v___y_558_;
v___y_522_ = v___y_559_;
v___y_523_ = v___y_560_;
v___y_524_ = v___y_561_;
v___y_525_ = v___y_562_;
v___y_526_ = v___y_565_;
v___y_527_ = v___y_564_;
v___y_528_ = v___y_567_;
v___y_529_ = v___y_569_;
v___y_530_ = v___y_568_;
v___y_531_ = v___y_573_;
v___y_532_ = v___y_572_;
v___y_533_ = v___y_574_;
v___y_534_ = v___x_577_;
goto v___jp_519_;
}
v___jp_578_:
{
if (v___y_584_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v___y_592_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; uint8_t v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_box(0);
lean_inc(v___y_580_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_596_);
lean_inc_ref(v___y_592_);
lean_inc_ref(v___y_593_);
lean_inc(v___y_595_);
lean_inc_ref(v___y_597_);
v___x_602_ = lean_apply_9(v___y_588_, v___x_601_, v___y_597_, v___y_595_, v___y_593_, v___y_592_, v___y_596_, v___y_585_, v___y_580_, lean_box(0));
v___y_520_ = v___y_579_;
v___y_521_ = v___y_580_;
v___y_522_ = v___y_581_;
v___y_523_ = v___y_582_;
v___y_524_ = v___y_583_;
v___y_525_ = v___y_584_;
v___y_526_ = v___y_587_;
v___y_527_ = v___y_586_;
v___y_528_ = v___y_589_;
v___y_529_ = v___y_591_;
v___y_530_ = v___y_590_;
v___y_531_ = v___y_595_;
v___y_532_ = v___y_594_;
v___y_533_ = v___y_596_;
v___y_534_ = v___x_602_;
goto v___jp_519_;
}
else
{
lean_object* v_name_603_; lean_object* v___x_604_; 
v_name_603_ = lean_ctor_get(v___y_583_, 0);
v___x_604_ = l_Lean_Meta_isInstance___redArg(v_name_603_, v___y_580_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; uint8_t v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
if (v___x_606_ == 0)
{
if (lean_obj_tag(v_name_603_) == 1)
{
lean_object* v_str_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_str_607_ = lean_ctor_get(v_name_603_, 1);
v___x_608_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0));
v___x_609_ = lean_string_dec_eq(v_str_607_, v___x_608_);
if (v___x_609_ == 0)
{
v___y_557_ = v___y_579_;
v___y_558_ = v___y_580_;
v___y_559_ = v___y_581_;
v___y_560_ = v___y_582_;
v___y_561_ = v___y_583_;
v___y_562_ = v___y_584_;
v___y_563_ = v___y_585_;
v___y_564_ = v___y_586_;
v___y_565_ = v___y_587_;
v___y_566_ = v___y_588_;
v___y_567_ = v___y_589_;
v___y_568_ = v___y_590_;
v___y_569_ = v___y_591_;
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
v___y_572_ = v___y_594_;
v___y_573_ = v___y_595_;
v___y_574_ = v___y_596_;
v___y_575_ = v___y_597_;
goto v___jp_556_;
}
else
{
lean_dec(v___y_594_);
lean_dec_ref(v___y_591_);
lean_dec_ref(v___y_588_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v___y_581_);
goto v___jp_435_;
}
}
else
{
v___y_557_ = v___y_579_;
v___y_558_ = v___y_580_;
v___y_559_ = v___y_581_;
v___y_560_ = v___y_582_;
v___y_561_ = v___y_583_;
v___y_562_ = v___y_584_;
v___y_563_ = v___y_585_;
v___y_564_ = v___y_586_;
v___y_565_ = v___y_587_;
v___y_566_ = v___y_588_;
v___y_567_ = v___y_589_;
v___y_568_ = v___y_590_;
v___y_569_ = v___y_591_;
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
v___y_572_ = v___y_594_;
v___y_573_ = v___y_595_;
v___y_574_ = v___y_596_;
v___y_575_ = v___y_597_;
goto v___jp_556_;
}
}
else
{
lean_dec(v___y_594_);
lean_dec_ref(v___y_591_);
lean_dec_ref(v___y_588_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v___y_581_);
goto v___jp_435_;
}
}
else
{
lean_dec_ref(v___y_588_);
v___y_520_ = v___y_579_;
v___y_521_ = v___y_580_;
v___y_522_ = v___y_581_;
v___y_523_ = v___y_582_;
v___y_524_ = v___y_583_;
v___y_525_ = v___y_584_;
v___y_526_ = v___y_587_;
v___y_527_ = v___y_586_;
v___y_528_ = v___y_589_;
v___y_529_ = v___y_591_;
v___y_530_ = v___y_590_;
v___y_531_ = v___y_595_;
v___y_532_ = v___y_594_;
v___y_533_ = v___y_596_;
v___y_534_ = v___x_604_;
goto v___jp_519_;
}
}
}
else
{
lean_dec_ref(v___y_588_);
v___y_520_ = v___y_579_;
v___y_521_ = v___y_580_;
v___y_522_ = v___y_581_;
v___y_523_ = v___y_582_;
v___y_524_ = v___y_583_;
v___y_525_ = v___y_584_;
v___y_526_ = v___y_587_;
v___y_527_ = v___y_586_;
v___y_528_ = v___y_589_;
v___y_529_ = v___y_591_;
v___y_530_ = v___y_590_;
v___y_531_ = v___y_595_;
v___y_532_ = v___y_594_;
v___y_533_ = v___y_596_;
v___y_534_ = v___x_598_;
goto v___jp_519_;
}
}
else
{
lean_dec_ref(v___y_588_);
v___y_473_ = v___y_580_;
v___y_474_ = v___y_581_;
v___y_475_ = v___y_582_;
v___y_476_ = v___y_583_;
v___y_477_ = v___y_587_;
v___y_478_ = v___y_586_;
v___y_479_ = v___y_589_;
v___y_480_ = v___y_591_;
v___y_481_ = v___y_590_;
v___y_482_ = v___y_595_;
v___y_483_ = v___y_594_;
v___y_484_ = v___y_596_;
goto v___jp_472_;
}
}
v___jp_610_:
{
lean_object* v_config_622_; uint8_t v_inlineDefs_623_; 
v_config_622_ = lean_ctor_get(v___y_615_, 1);
v_inlineDefs_623_ = lean_ctor_get_uint8(v_config_622_, 3);
if (v_inlineDefs_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
lean_dec(v_declName_611_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
uint8_t v_inlinePartial_626_; lean_object* v___x_627_; 
v_inlinePartial_626_ = lean_ctor_get_uint8(v_config_622_, 1);
v___x_627_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_618_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; uint8_t v___x_629_; lean_object* v___x_630_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = lean_unbox(v_a_628_);
v___x_630_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_611_, v___x_629_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_653_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_653_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_653_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_653_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
if (lean_obj_tag(v_a_631_) == 1)
{
lean_object* v_val_635_; uint8_t v___x_636_; uint8_t v___x_637_; 
v_val_635_ = lean_ctor_get(v_a_631_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v_a_631_, 1);
v___x_636_ = lean_unbox(v_a_628_);
lean_dec(v_a_628_);
v___x_637_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v_value_638_; 
v_value_638_ = lean_ctor_get(v_val_635_, 1);
if (lean_obj_tag(v_value_638_) == 0)
{
lean_object* v_toSignature_639_; uint8_t v_recursive_640_; lean_object* v_code_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___f_646_; 
lean_del_object(v___x_633_);
v_toSignature_639_ = lean_ctor_get(v_val_635_, 0);
lean_inc_ref(v_toSignature_639_);
v_recursive_640_ = lean_ctor_get_uint8(v_val_635_, sizeof(void*)*3);
v_code_641_ = lean_ctor_get(v_value_638_, 0);
lean_inc_ref_n(v_code_641_, 2);
v___x_642_ = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_635_);
v___x_643_ = lean_box(v___x_642_);
v___x_644_ = lean_box(v_mustInline_438_);
v___x_645_ = lean_box(v_inlineDefs_623_);
lean_inc(v_val_635_);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed), 14, 5);
lean_closure_set(v___f_646_, 0, v_val_635_);
lean_closure_set(v___f_646_, 1, v___x_643_);
lean_closure_set(v___f_646_, 2, v_code_641_);
lean_closure_set(v___f_646_, 3, v___x_644_);
lean_closure_set(v___f_646_, 4, v___x_645_);
if (v___x_642_ == 0)
{
if (v_recursive_640_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
v___y_579_ = v_inlinePartial_626_;
v___y_580_ = v___y_621_;
v___y_581_ = v_val_635_;
v___y_582_ = v___x_647_;
v___y_583_ = v_toSignature_639_;
v___y_584_ = v_mustInline_614_;
v___y_585_ = v___y_620_;
v___y_586_ = v_code_641_;
v___y_587_ = v___x_642_;
v___y_588_ = v___f_646_;
v___y_589_ = v_recursive_640_;
v___y_590_ = v___x_637_;
v___y_591_ = v_args_613_;
v___y_592_ = v___y_618_;
v___y_593_ = v___y_617_;
v___y_594_ = v_us_612_;
v___y_595_ = v___y_616_;
v___y_596_ = v___y_619_;
v___y_597_ = v___y_615_;
goto v___jp_578_;
}
else
{
lean_dec_ref(v___f_646_);
lean_dec_ref(v_code_641_);
lean_dec_ref(v_toSignature_639_);
lean_dec(v_val_635_);
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
goto v___jp_435_;
}
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_box(0);
v___y_579_ = v_inlinePartial_626_;
v___y_580_ = v___y_621_;
v___y_581_ = v_val_635_;
v___y_582_ = v___x_648_;
v___y_583_ = v_toSignature_639_;
v___y_584_ = v_mustInline_614_;
v___y_585_ = v___y_620_;
v___y_586_ = v_code_641_;
v___y_587_ = v___x_642_;
v___y_588_ = v___f_646_;
v___y_589_ = v_recursive_640_;
v___y_590_ = v___x_637_;
v___y_591_ = v_args_613_;
v___y_592_ = v___y_618_;
v___y_593_ = v___y_617_;
v___y_594_ = v_us_612_;
v___y_595_ = v___y_616_;
v___y_596_ = v___y_619_;
v___y_597_ = v___y_615_;
goto v___jp_578_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v_val_635_);
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
v___x_649_ = lean_box(0);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_649_);
v___x_651_ = v___x_633_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_dec(v_val_635_);
lean_del_object(v___x_633_);
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
goto v___jp_432_;
}
}
else
{
lean_del_object(v___x_633_);
lean_dec(v_a_631_);
lean_dec(v_a_628_);
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
goto v___jp_432_;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_a_628_);
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
v_a_654_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_630_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_630_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_args_613_);
lean_dec(v_us_612_);
lean_dec(v_declName_611_);
v_a_662_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_627_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_627_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
v___jp_670_:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v___y_672_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v_subst_682_; lean_object* v_used_683_; lean_object* v_binderRenaming_684_; lean_object* v_funDeclInfoMap_685_; uint8_t v_simplified_686_; lean_object* v_visited_687_; lean_object* v_inline_688_; lean_object* v_inlineLocal_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref_known(v___x_680_, 1);
v___x_681_ = lean_st_ref_take(v___y_672_);
v_subst_682_ = lean_ctor_get(v___x_681_, 0);
v_used_683_ = lean_ctor_get(v___x_681_, 1);
v_binderRenaming_684_ = lean_ctor_get(v___x_681_, 2);
v_funDeclInfoMap_685_ = lean_ctor_get(v___x_681_, 3);
v_simplified_686_ = lean_ctor_get_uint8(v___x_681_, sizeof(void*)*7);
v_visited_687_ = lean_ctor_get(v___x_681_, 4);
v_inline_688_ = lean_ctor_get(v___x_681_, 5);
v_inlineLocal_689_ = lean_ctor_get(v___x_681_, 6);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_720_ == 0)
{
v___x_691_ = v___x_681_;
v_isShared_692_ = v_isSharedCheck_720_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_inlineLocal_689_);
lean_inc(v_inline_688_);
lean_inc(v_visited_687_);
lean_inc(v_funDeclInfoMap_685_);
lean_inc(v_binderRenaming_684_);
lean_inc(v_used_683_);
lean_inc(v_subst_682_);
lean_dec(v___x_681_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_720_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_add(v_inlineLocal_689_, v___x_693_);
lean_dec(v_inlineLocal_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 6, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_subst_682_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_used_683_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_binderRenaming_684_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_funDeclInfoMap_685_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_visited_687_);
lean_ctor_set(v_reuseFailAlloc_719_, 5, v_inline_688_);
lean_ctor_set(v_reuseFailAlloc_719_, 6, v___x_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*7, v_simplified_686_);
v___x_696_ = v_reuseFailAlloc_719_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_st_ref_put(v___y_672_, v___x_696_);
v___x_698_ = l_Lean_Compiler_LCNF_getType(v___y_673_, v___y_679_, v___y_678_, v___y_676_, v___y_675_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_710_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_710_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_710_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_710_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_params_703_; lean_object* v_value_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v_params_703_ = lean_ctor_get(v___y_671_, 2);
lean_inc_ref(v_params_703_);
v_value_704_ = lean_ctor_get(v___y_671_, 4);
lean_inc_ref(v_value_704_);
lean_dec_ref(v___y_671_);
v___x_705_ = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(v___x_705_, 0, v_params_703_);
lean_ctor_set(v___x_705_, 1, v_value_704_);
lean_ctor_set(v___x_705_, 2, v_a_699_);
lean_ctor_set(v___x_705_, 3, v___y_677_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*4, v___y_674_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*4 + 1, v_mustInline_438_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*4 + 2, v_mustInline_438_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_706_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___y_677_);
lean_dec_ref(v___y_671_);
v_a_711_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_698_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_698_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___y_677_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_671_);
v_a_721_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_680_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_680_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
v___jp_729_:
{
uint8_t v___x_739_; lean_object* v___x_740_; 
v___x_739_ = 1;
v___x_740_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v___y_731_, v___y_730_, v___y_738_);
if (lean_obj_tag(v___x_740_) == 0)
{
if (v___y_732_ == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_750_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_750_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_750_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_750_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v___x_745_; 
v___x_745_ = lean_unbox(v_a_741_);
lean_dec(v_a_741_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec_ref(v___y_736_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_731_);
v___x_746_ = lean_box(0);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_del_object(v___x_743_);
v___y_671_ = v___y_731_;
v___y_672_ = v___y_730_;
v___y_673_ = v___y_733_;
v___y_674_ = v___x_739_;
v___y_675_ = v___y_734_;
v___y_676_ = v___y_735_;
v___y_677_ = v___y_736_;
v___y_678_ = v___y_737_;
v___y_679_ = v___y_738_;
goto v___jp_670_;
}
}
}
else
{
lean_dec_ref_known(v___x_740_, 1);
v___y_671_ = v___y_731_;
v___y_672_ = v___y_730_;
v___y_673_ = v___y_733_;
v___y_674_ = v___x_739_;
v___y_675_ = v___y_734_;
v___y_676_ = v___y_735_;
v___y_677_ = v___y_736_;
v___y_678_ = v___y_737_;
v___y_679_ = v___y_738_;
goto v___jp_670_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v___y_736_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_731_);
v_a_751_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_740_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_740_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_759_:
{
uint8_t v___x_768_; lean_object* v___x_769_; 
v___x_768_ = 0;
lean_inc(v_fvarId_760_);
v___x_769_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_768_, v_fvarId_760_, v___y_765_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_787_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
if (lean_obj_tag(v_a_770_) == 1)
{
if (v_mustInline_762_ == 0)
{
lean_object* v_val_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_val_774_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v_a_770_, 1);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_array_get_size(v_args_761_);
v___x_777_ = lean_nat_dec_lt(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_val_774_);
lean_dec_ref(v_args_761_);
lean_dec(v_fvarId_760_);
v___x_778_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_778_);
v___x_780_ = v___x_772_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_del_object(v___x_772_);
v___y_730_ = v___y_763_;
v___y_731_ = v_val_774_;
v___y_732_ = v_mustInline_762_;
v___y_733_ = v_fvarId_760_;
v___y_734_ = v___y_767_;
v___y_735_ = v___y_766_;
v___y_736_ = v_args_761_;
v___y_737_ = v___y_765_;
v___y_738_ = v___y_764_;
goto v___jp_729_;
}
}
else
{
lean_object* v_val_782_; 
lean_del_object(v___x_772_);
v_val_782_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v_a_770_, 1);
v___y_730_ = v___y_763_;
v___y_731_ = v_val_782_;
v___y_732_ = v_mustInline_762_;
v___y_733_ = v_fvarId_760_;
v___y_734_ = v___y_767_;
v___y_735_ = v___y_766_;
v___y_736_ = v_args_761_;
v___y_737_ = v___y_765_;
v___y_738_ = v___y_764_;
goto v___jp_729_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_785_; 
lean_dec(v_a_770_);
lean_dec_ref(v_args_761_);
lean_dec(v_fvarId_760_);
v___x_783_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_783_);
v___x_785_ = v___x_772_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_args_761_);
lean_dec(v_fvarId_760_);
v_a_788_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_769_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_769_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
v___jp_796_:
{
if (lean_obj_tag(v_e_797_) == 3)
{
lean_object* v_declName_806_; lean_object* v_us_807_; lean_object* v_args_808_; 
v_declName_806_ = lean_ctor_get(v_e_797_, 0);
lean_inc(v_declName_806_);
v_us_807_ = lean_ctor_get(v_e_797_, 1);
lean_inc(v_us_807_);
v_args_808_ = lean_ctor_get(v_e_797_, 2);
lean_inc_ref(v_args_808_);
lean_dec_ref_known(v_e_797_, 3);
v_declName_611_ = v_declName_806_;
v_us_612_ = v_us_807_;
v_args_613_ = v_args_808_;
v_mustInline_614_ = v_mustInline_798_;
v___y_615_ = v___y_799_;
v___y_616_ = v___y_800_;
v___y_617_ = v___y_801_;
v___y_618_ = v___y_802_;
v___y_619_ = v___y_803_;
v___y_620_ = v___y_804_;
v___y_621_ = v___y_805_;
goto v___jp_610_;
}
else
{
if (lean_obj_tag(v_e_797_) == 4)
{
lean_object* v_fvarId_809_; lean_object* v_args_810_; 
v_fvarId_809_ = lean_ctor_get(v_e_797_, 0);
lean_inc(v_fvarId_809_);
v_args_810_ = lean_ctor_get(v_e_797_, 1);
lean_inc_ref(v_args_810_);
lean_dec_ref_known(v_e_797_, 2);
v_fvarId_760_ = v_fvarId_809_;
v_args_761_ = v_args_810_;
v_mustInline_762_ = v_mustInline_798_;
v___y_763_ = v___y_800_;
v___y_764_ = v___y_802_;
v___y_765_ = v___y_803_;
v___y_766_ = v___y_804_;
v___y_767_ = v___y_805_;
goto v___jp_759_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_e_797_);
v___x_811_ = lean_box(0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_423_ = stack[0].m_obj;
lean_object* v_a_424_ = stack[1].m_obj;
lean_object* v_a_425_ = stack[2].m_obj;
lean_object* v_a_426_ = stack[3].m_obj;
lean_object* v_a_427_ = stack[4].m_obj;
lean_object* v_a_428_ = stack[5].m_obj;
lean_object* v_a_429_ = stack[6].m_obj;
lean_object* v_a_430_ = stack[7].m_obj;
lean_object* v_res_940_;
v_res_940_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___boxed(lean_object* v_e_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_e_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_950_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_));
v___x_1034_ = 0;
v___x_1035_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_));
v___x_1036_ = l_Lean_registerTraceClass(v___x_1033_, v___x_1034_, v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1037_;
v_res_1037_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2____boxed(lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
return v_res_1039_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
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
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
}
#ifdef __cplusplus
}
#endif
