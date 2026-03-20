// Lean compiler output
// Module: Lean.Meta.Sym.Simp.SimpM
// Imports: public import Lean.Meta.Sym.Pattern
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedResult_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedResult = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41;
static const lean_string_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<default>"};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Sym_Simp_Result_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
uint8_t v_done_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_done_8_ = lean_ctor_get_uint8(v_t_6_, 0);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_box(v_done_8_);
v___x_10_ = lean_apply_1(v_k_7_, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_e_x27_11_; lean_object* v_proof_12_; uint8_t v_done_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_e_x27_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_e_x27_11_);
v_proof_12_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_proof_12_);
v_done_13_ = lean_ctor_get_uint8(v_t_6_, sizeof(void*)*2);
lean_dec_ref(v_t_6_);
v___x_14_ = lean_box(v_done_13_);
v___x_15_ = lean_apply_3(v_k_7_, v_e_x27_11_, v_proof_12_, v___x_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_Sym_Simp_Result_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_24_, v_h_25_, v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim___redArg(lean_object* v_t_28_, lean_object* v_rfl_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_28_, v_rfl_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_rfl_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_32_, v_rfl_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim___redArg(lean_object* v_t_36_, lean_object* v_step_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_36_, v_step_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_step_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_40_, v_step_42_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0);
v___x_51_ = l_ReaderT_instMonad___redArg(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6(void){
_start:
{
lean_object* v___x_56_; lean_object* v___f_57_; 
v___x_56_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_57_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_57_, 0, v___x_56_);
return v___f_57_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7(void){
_start:
{
lean_object* v___x_58_; lean_object* v___f_59_; 
v___x_58_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_59_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_59_, 0, v___x_58_);
return v___f_59_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8(void){
_start:
{
lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___x_62_; 
v___f_60_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7);
v___f_61_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___f_61_);
lean_ctor_set(v___x_62_, 1, v___f_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9(void){
_start:
{
lean_object* v___x_63_; lean_object* v___f_64_; 
v___x_63_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8);
v___f_64_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_64_, 0, v___x_63_);
return v___f_64_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10(void){
_start:
{
lean_object* v___x_65_; lean_object* v___f_66_; 
v___x_65_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8);
v___f_66_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_66_, 0, v___x_65_);
return v___f_66_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11(void){
_start:
{
lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
v___f_67_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10);
v___f_68_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___f_68_);
lean_ctor_set(v___x_69_, 1, v___f_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12(void){
_start:
{
lean_object* v___x_70_; lean_object* v___f_71_; 
v___x_70_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11);
v___f_71_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_71_, 0, v___x_70_);
return v___f_71_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13(void){
_start:
{
lean_object* v___x_72_; lean_object* v___f_73_; 
v___x_72_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11);
v___f_73_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_73_, 0, v___x_72_);
return v___f_73_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14(void){
_start:
{
lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v___f_74_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13);
v___f_75_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___f_75_);
lean_ctor_set(v___x_76_, 1, v___f_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15(void){
_start:
{
lean_object* v___x_77_; lean_object* v___f_78_; 
v___x_77_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14);
v___f_78_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_78_, 0, v___x_77_);
return v___f_78_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16(void){
_start:
{
lean_object* v___x_79_; lean_object* v___f_80_; 
v___x_79_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14);
v___f_80_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_80_, 0, v___x_79_);
return v___f_80_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17(void){
_start:
{
lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_83_; 
v___f_81_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16);
v___f_82_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___f_82_);
lean_ctor_set(v___x_83_, 1, v___f_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18(void){
_start:
{
lean_object* v___x_84_; lean_object* v___f_85_; 
v___x_84_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17);
v___f_85_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_85_, 0, v___x_84_);
return v___f_85_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19(void){
_start:
{
lean_object* v___x_86_; lean_object* v___f_87_; 
v___x_86_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17);
v___f_87_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_87_, 0, v___x_86_);
return v___f_87_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20(void){
_start:
{
lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___x_90_; 
v___f_88_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19);
v___f_89_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v___f_89_);
lean_ctor_set(v___x_90_, 1, v___f_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21(void){
_start:
{
lean_object* v___x_91_; lean_object* v___f_92_; 
v___x_91_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_92_, 0, v___x_91_);
return v___f_92_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22(void){
_start:
{
lean_object* v___x_93_; lean_object* v___f_94_; 
v___x_93_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_94_, 0, v___x_93_);
return v___f_94_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23(void){
_start:
{
lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
v___f_95_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22);
v___f_96_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___f_96_);
lean_ctor_set(v___x_97_, 1, v___f_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24(void){
_start:
{
lean_object* v___x_98_; lean_object* v___f_99_; 
v___x_98_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23);
v___f_99_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_99_, 0, v___x_98_);
return v___f_99_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25(void){
_start:
{
lean_object* v___x_100_; lean_object* v___f_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23);
v___f_101_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_101_, 0, v___x_100_);
return v___f_101_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26(void){
_start:
{
lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; 
v___f_102_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25);
v___f_103_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___f_103_);
lean_ctor_set(v___x_104_, 1, v___f_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; 
v___x_108_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_109_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_110_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_111_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_110_, v___x_109_, v___x_108_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31(void){
_start:
{
lean_object* v___x_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30);
v___f_113_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_114_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_115_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_114_, v___f_113_, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31);
v___x_117_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_118_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_119_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_118_, v___x_117_, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33(void){
_start:
{
lean_object* v___x_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32);
v___f_121_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_122_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_123_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_122_, v___f_121_, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v___x_124_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33);
v___x_125_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_126_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_127_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_126_, v___x_125_, v___x_124_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35(void){
_start:
{
lean_object* v___x_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___x_131_; 
v___x_128_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34);
v___f_129_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_130_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_131_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_130_, v___f_129_, v___x_128_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36(void){
_start:
{
lean_object* v___x_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35);
v___f_133_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_134_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_135_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_134_, v___f_133_, v___x_132_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___f_138_; 
v___x_136_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___x_137_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_138_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_138_, 0, v___x_137_);
lean_closure_set(v___f_138_, 1, v___x_136_);
return v___f_138_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38(void){
_start:
{
lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; 
v___f_139_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_140_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_141_, 0, v___f_140_);
lean_closure_set(v___f_141_, 1, v___f_139_);
return v___f_141_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39(void){
_start:
{
lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v___f_144_; 
v___x_142_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_143_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_144_, 0, v___f_143_);
lean_closure_set(v___f_144_, 1, v___x_142_);
return v___f_144_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40(void){
_start:
{
lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___f_147_; 
v___f_145_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_146_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_147_, 0, v___f_146_);
lean_closure_set(v___f_147_, 1, v___f_145_);
return v___f_147_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41(void){
_start:
{
lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___f_150_; 
v___f_148_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_149_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40);
v___f_150_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_150_, 0, v___f_149_);
lean_closure_set(v___f_150_, 1, v___f_148_);
return v___f_150_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42));
v___x_153_ = l_Lean_stringToMessageData(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object* v_00_u03b1_154_){
_start:
{
lean_object* v___x_155_; lean_object* v_toApplicative_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_226_; 
v___x_155_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1);
v_toApplicative_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v___x_155_, 1);
lean_dec(v_unused_227_);
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_226_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_toApplicative_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_226_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_toFunctor_160_; lean_object* v_toSeq_161_; lean_object* v_toSeqLeft_162_; lean_object* v_toSeqRight_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_224_; 
v_toFunctor_160_ = lean_ctor_get(v_toApplicative_156_, 0);
v_toSeq_161_ = lean_ctor_get(v_toApplicative_156_, 2);
v_toSeqLeft_162_ = lean_ctor_get(v_toApplicative_156_, 3);
v_toSeqRight_163_ = lean_ctor_get(v_toApplicative_156_, 4);
v_isSharedCheck_224_ = !lean_is_exclusive(v_toApplicative_156_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v_toApplicative_156_, 1);
lean_dec(v_unused_225_);
v___x_165_ = v_toApplicative_156_;
v_isShared_166_ = v_isSharedCheck_224_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_toSeqRight_163_);
lean_inc(v_toSeqLeft_162_);
lean_inc(v_toSeq_161_);
lean_inc(v_toFunctor_160_);
lean_dec(v_toApplicative_156_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_224_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_176_; 
v___f_167_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2));
v___f_168_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3));
lean_inc_ref(v_toFunctor_160_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_169_, 0, v_toFunctor_160_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_170_, 0, v_toFunctor_160_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___f_169_);
lean_ctor_set(v___x_171_, 1, v___f_170_);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_172_, 0, v_toSeqRight_163_);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_173_, 0, v_toSeqLeft_162_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_174_, 0, v_toSeq_161_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 4, v___f_172_);
lean_ctor_set(v___x_165_, 3, v___f_173_);
lean_ctor_set(v___x_165_, 2, v___f_174_);
lean_ctor_set(v___x_165_, 1, v___f_167_);
lean_ctor_set(v___x_165_, 0, v___x_171_);
v___x_176_ = v___x_165_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v___f_174_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v___f_173_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v___f_172_);
v___x_176_ = v_reuseFailAlloc_223_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___f_168_);
lean_ctor_set(v___x_158_, 0, v___x_176_);
v___x_178_ = v___x_158_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___f_168_);
v___x_178_ = v_reuseFailAlloc_222_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v_toApplicative_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_220_; 
v___x_179_ = l_ReaderT_instMonad___redArg(v___x_178_);
v_toApplicative_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v___x_179_, 1);
lean_dec(v_unused_221_);
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_220_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_toApplicative_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_220_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_toFunctor_184_; lean_object* v_toSeq_185_; lean_object* v_toSeqLeft_186_; lean_object* v_toSeqRight_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_218_; 
v_toFunctor_184_ = lean_ctor_get(v_toApplicative_180_, 0);
v_toSeq_185_ = lean_ctor_get(v_toApplicative_180_, 2);
v_toSeqLeft_186_ = lean_ctor_get(v_toApplicative_180_, 3);
v_toSeqRight_187_ = lean_ctor_get(v_toApplicative_180_, 4);
v_isSharedCheck_218_ = !lean_is_exclusive(v_toApplicative_180_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_dec(v_unused_219_);
v___x_189_ = v_toApplicative_180_;
v_isShared_190_ = v_isSharedCheck_218_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_toSeqRight_187_);
lean_inc(v_toSeqLeft_186_);
lean_inc(v_toSeq_185_);
lean_inc(v_toFunctor_184_);
lean_dec(v_toApplicative_180_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_218_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_200_; 
v___f_191_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4));
v___f_192_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5));
lean_inc_ref(v_toFunctor_184_);
v___f_193_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_193_, 0, v_toFunctor_184_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_194_, 0, v_toFunctor_184_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___f_193_);
lean_ctor_set(v___x_195_, 1, v___f_194_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_196_, 0, v_toSeqRight_187_);
v___f_197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_197_, 0, v_toSeqLeft_186_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeq_185_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v___f_196_);
lean_ctor_set(v___x_189_, 3, v___f_197_);
lean_ctor_set(v___x_189_, 2, v___f_198_);
lean_ctor_set(v___x_189_, 1, v___f_191_);
lean_ctor_set(v___x_189_, 0, v___x_195_);
v___x_200_ = v___x_189_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v___f_198_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___f_197_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v___f_196_);
v___x_200_ = v_reuseFailAlloc_217_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v___f_192_);
lean_ctor_set(v___x_182_, 0, v___x_200_);
v___x_202_ = v___x_182_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___f_192_);
v___x_202_ = v_reuseFailAlloc_216_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_toMonadRef_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_203_ = l_ReaderT_instMonad___redArg(v___x_202_);
v___x_204_ = l_ReaderT_instMonad___redArg(v___x_203_);
v___x_205_ = l_ReaderT_instMonad___redArg(v___x_204_);
v___x_206_ = l_ReaderT_instMonad___redArg(v___x_205_);
v___x_207_ = l_ReaderT_instMonad___redArg(v___x_206_);
v___x_208_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26);
v___x_209_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36);
v_toMonadRef_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_toMonadRef_210_);
v___f_211_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41);
lean_inc_ref(v___x_207_);
v___x_212_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_211_, v___x_207_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_208_);
lean_ctor_set(v___x_213_, 1, v_toMonadRef_210_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
v___x_214_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43);
v___x_215_ = l_Lean_throwError___redArg(v___x_207_, v___x_213_, v___x_214_);
return v___x_215_;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v_env_235_; lean_object* v___x_236_; lean_object* v_mctx_237_; lean_object* v_lctx_238_; lean_object* v_options_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_234_ = lean_st_ref_get(v___y_232_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_env_235_);
lean_dec(v___x_234_);
v___x_236_ = lean_st_ref_get(v___y_230_);
v_mctx_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_mctx_237_);
lean_dec(v___x_236_);
v_lctx_238_ = lean_ctor_get(v___y_229_, 2);
v_options_239_ = lean_ctor_get(v___y_231_, 2);
lean_inc_ref(v_options_239_);
lean_inc_ref(v_lctx_238_);
v___x_240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_240_, 0, v_env_235_);
lean_ctor_set(v___x_240_, 1, v_mctx_237_);
lean_ctor_set(v___x_240_, 2, v_lctx_238_);
lean_ctor_set(v___x_240_, 3, v_options_239_);
v___x_241_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_msgData_228_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0___boxed(lean_object* v_msgData_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msgData_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_ref_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_ref_256_ = lean_ctor_get(v___y_253_, 5);
v___x_257_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_ref_256_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_ref_256_);
lean_ctor_set(v___x_262_, 1, v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg___boxed(lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43);
v___x_286_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v___x_285_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v_x_287_);
return v_res_298_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1(void){
_start:
{
uint8_t v___x_300_; lean_object* v___f_301_; lean_object* v___x_302_; 
v___x_300_ = 0;
v___f_301_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0));
v___x_302_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_302_, 0, v___f_301_);
lean_ctor_set(v___x_302_, 1, v___f_301_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*2, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(lean_object* v_00_u03b1_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_305_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___boxed(lean_object* v_00_u03b1_317_, lean_object* v_msg_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(v_00_u03b1_317_, v_msg_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default;
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object* v_m_331_){
_start:
{
lean_inc_ref(v_m_331_);
return v_m_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_332_);
lean_dec_ref(v_m_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object* v_m_334_){
_start:
{
lean_inc(v_m_334_);
return v_m_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_335_);
lean_dec(v_m_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_a_343_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object* v_x_365_, lean_object* v_methods_366_, lean_object* v_config_367_, lean_object* v_s_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_lctx_377_; lean_object* v_decls_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_406_; 
v___x_376_ = lean_st_mk_ref(v_s_368_);
v_lctx_377_ = lean_ctor_get(v_a_371_, 2);
lean_inc_ref(v_lctx_377_);
v_decls_378_ = lean_ctor_get(v_lctx_377_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_lctx_377_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_407_ = lean_ctor_get(v_lctx_377_, 2);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_lctx_377_, 0);
lean_dec(v_unused_408_);
v___x_380_ = v_lctx_377_;
v_isShared_381_ = v_isSharedCheck_406_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_decls_378_);
lean_dec(v_lctx_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_406_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_size_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v_size_382_ = lean_ctor_get(v_decls_378_, 2);
lean_inc(v_size_382_);
lean_dec_ref(v_decls_378_);
v___x_383_ = lean_unsigned_to_nat(0u);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_383_);
lean_ctor_set(v___x_380_, 1, v_size_382_);
lean_ctor_set(v___x_380_, 0, v_config_367_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_config_367_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_size_382_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v___x_383_);
v___x_385_ = v_reuseFailAlloc_405_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
lean_inc(v___x_376_);
v___x_386_ = lean_apply_10(v_x_365_, v_methods_366_, v___x_385_, v___x_376_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, lean_box(0));
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_396_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_396_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_st_ref_get(v___x_376_);
lean_dec(v___x_376_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_387_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v___x_376_);
v_a_397_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_386_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_386_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object* v_x_409_, lean_object* v_methods_410_, lean_object* v_config_411_, lean_object* v_s_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_409_, v_methods_410_, v_config_411_, v_s_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object* v_00_u03b1_421_, lean_object* v_x_422_, lean_object* v_methods_423_, lean_object* v_config_424_, lean_object* v_s_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_422_, v_methods_423_, v_config_424_, v_s_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object* v_00_u03b1_434_, lean_object* v_x_435_, lean_object* v_methods_436_, lean_object* v_config_437_, lean_object* v_s_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_Sym_Simp_SimpM_run(v_00_u03b1_434_, v_x_435_, v_methods_436_, v_config_437_, v_s_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v_res_446_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__1);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object* v_x_453_, lean_object* v_methods_454_, lean_object* v_config_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_lctx_463_; lean_object* v_decls_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_485_; 
v_lctx_463_ = lean_ctor_get(v_a_458_, 2);
lean_inc_ref(v_lctx_463_);
v_decls_464_ = lean_ctor_get(v_lctx_463_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_lctx_463_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; 
v_unused_486_ = lean_ctor_get(v_lctx_463_, 2);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_lctx_463_, 0);
lean_dec(v_unused_487_);
v___x_466_ = v_lctx_463_;
v_isShared_467_ = v_isSharedCheck_485_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_decls_464_);
lean_dec(v_lctx_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_485_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_size_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v_size_468_ = lean_ctor_get(v_decls_464_, 2);
lean_inc(v_size_468_);
lean_dec_ref(v_decls_464_);
v___x_469_ = lean_unsigned_to_nat(0u);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 2, v___x_469_);
lean_ctor_set(v___x_466_, 1, v_size_468_);
lean_ctor_set(v___x_466_, 0, v_config_455_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_config_455_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_size_468_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v___x_469_);
v___x_471_ = v_reuseFailAlloc_484_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__2, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__2);
v___x_473_ = lean_st_mk_ref(v___x_472_);
lean_inc(v___x_473_);
v___x_474_ = lean_apply_10(v_x_453_, v_methods_454_, v___x_471_, v___x_473_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, lean_box(0));
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_483_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_st_ref_get(v___x_473_);
lean_dec(v___x_473_);
lean_dec(v___x_479_);
if (v_isShared_478_ == 0)
{
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_475_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_dec(v___x_473_);
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object* v_x_488_, lean_object* v_methods_489_, lean_object* v_config_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_488_, v_methods_489_, v_config_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object* v_00_u03b1_499_, lean_object* v_x_500_, lean_object* v_methods_501_, lean_object* v_config_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_500_, v_methods_501_, v_config_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object* v_00_u03b1_511_, lean_object* v_x_512_, lean_object* v_methods_513_, lean_object* v_config_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(v_00_u03b1_511_, v_x_512_, v_methods_513_, v_config_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object* v_a_00___x40___internal___hyg_534_, lean_object* v_a_00___x40___internal___hyg_535_, lean_object* v_a_00___x40___internal___hyg_536_, lean_object* v_a_00___x40___internal___hyg_537_, lean_object* v_a_00___x40___internal___hyg_538_, lean_object* v_a_00___x40___internal___hyg_539_, lean_object* v_a_00___x40___internal___hyg_540_, lean_object* v_a_00___x40___internal___hyg_541_, lean_object* v_a_00___x40___internal___hyg_542_, lean_object* v_a_00___x40___internal___hyg_543_, lean_object* v_a_00___x40___internal___hyg_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = lean_sym_simp(v_a_00___x40___internal___hyg_534_, v_a_00___x40___internal___hyg_535_, v_a_00___x40___internal___hyg_536_, v_a_00___x40___internal___hyg_537_, v_a_00___x40___internal___hyg_538_, v_a_00___x40___internal___hyg_539_, v_a_00___x40___internal___hyg_540_, v_a_00___x40___internal___hyg_541_, v_a_00___x40___internal___hyg_542_, v_a_00___x40___internal___hyg_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object* v_a_546_){
_start:
{
lean_object* v_config_548_; lean_object* v___x_549_; 
v_config_548_ = lean_ctor_get(v_a_546_, 0);
lean_inc_ref(v_config_548_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_config_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_550_);
lean_dec_ref(v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_554_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache___redArg(lean_object* v_a_575_){
_start:
{
lean_object* v___x_577_; lean_object* v_cache_578_; lean_object* v___x_579_; 
v___x_577_ = lean_st_ref_get(v_a_575_);
v_cache_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc_ref(v_cache_578_);
lean_dec(v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v_cache_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache___redArg___boxed(lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_Sym_Simp_getCache___redArg(v_a_580_);
lean_dec(v_a_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache(lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; lean_object* v_cache_594_; lean_object* v___x_595_; 
v___x_593_ = lean_st_ref_get(v_a_585_);
v_cache_594_ = lean_ctor_get(v___x_593_, 1);
lean_inc_ref(v_cache_594_);
lean_dec(v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_cache_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getCache___boxed(lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Sym_Simp_getCache(v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_pre_618_; lean_object* v___x_619_; 
v_pre_618_ = lean_ctor_get(v_a_608_, 0);
lean_inc_ref(v_pre_618_);
v___x_619_ = lean_apply_11(v_pre_618_, v_e_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, lean_box(0));
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Meta_Sym_Simp_pre(v_e_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object* v_e_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_post_643_; lean_object* v___x_644_; 
v_post_643_ = lean_ctor_get(v_a_633_, 1);
lean_inc_ref(v_post_643_);
v___x_644_ = lean_apply_11(v_post_643_, v_e_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, lean_box(0));
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Sym_Simp_post(v_e_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object* v_a_657_, lean_object* v_cache_658_, lean_object* v_funext_659_, lean_object* v_a_x3f_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_numSteps_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_673_; 
v___x_662_ = lean_st_ref_take(v_a_657_);
v_numSteps_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; 
v_unused_674_ = lean_ctor_get(v___x_662_, 2);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_675_);
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_numSteps_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 2, v_funext_659_);
lean_ctor_set(v___x_665_, 1, v_cache_658_);
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_numSteps_663_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_cache_658_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_funext_659_);
v___x_668_ = v_reuseFailAlloc_672_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_st_ref_set(v_a_657_, v___x_668_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object* v_a_676_, lean_object* v_cache_677_, lean_object* v_funext_678_, lean_object* v_a_x3f_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_676_, v_cache_677_, v_funext_678_, v_a_x3f_679_);
lean_dec(v_a_x3f_679_);
lean_dec(v_a_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object* v_k_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_cache_695_; lean_object* v_funext_696_; lean_object* v_r_697_; 
v___x_693_ = lean_st_ref_get(v_a_685_);
v___x_694_ = lean_st_ref_get(v_a_685_);
v_cache_695_ = lean_ctor_get(v___x_693_, 1);
lean_inc_ref(v_cache_695_);
lean_dec(v___x_693_);
v_funext_696_ = lean_ctor_get(v___x_694_, 2);
lean_inc_ref(v_funext_696_);
lean_dec(v___x_694_);
lean_inc(v_a_685_);
v_r_697_ = lean_apply_10(v_k_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, lean_box(0));
if (lean_obj_tag(v_r_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_714_; 
v_a_698_ = lean_ctor_get(v_r_697_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_r_697_);
if (v_isSharedCheck_714_ == 0)
{
v___x_700_ = v_r_697_;
v_isShared_701_ = v_isSharedCheck_714_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v_r_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_714_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
lean_inc(v_a_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 1);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_713_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v___x_704_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_685_, v_cache_695_, v_funext_696_, v___x_703_);
lean_dec_ref(v___x_703_);
lean_dec(v_a_685_);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v___x_704_, 0);
lean_dec(v_unused_712_);
v___x_706_ = v___x_704_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_dec(v___x_704_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v_a_698_);
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_698_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_715_ = lean_ctor_get(v_r_697_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v_r_697_);
v___x_716_ = lean_box(0);
v___x_717_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_685_, v_cache_695_, v_funext_696_, v___x_716_);
lean_dec(v_a_685_);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_725_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 1);
lean_ctor_set(v___x_719_, 0, v_a_715_);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_715_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object* v_k_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object* v_00_u03b1_738_, lean_object* v_k_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_cache_752_; lean_object* v_funext_753_; lean_object* v_r_754_; 
v___x_750_ = lean_st_ref_get(v_a_742_);
v___x_751_ = lean_st_ref_get(v_a_742_);
v_cache_752_ = lean_ctor_get(v___x_750_, 1);
lean_inc_ref(v_cache_752_);
lean_dec(v___x_750_);
v_funext_753_ = lean_ctor_get(v___x_751_, 2);
lean_inc_ref(v_funext_753_);
lean_dec(v___x_751_);
lean_inc(v_a_742_);
v_r_754_ = lean_apply_10(v_k_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, lean_box(0));
if (lean_obj_tag(v_r_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_771_; 
v_a_755_ = lean_ctor_get(v_r_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_r_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_757_ = v_r_754_;
v_isShared_758_ = v_isSharedCheck_771_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_r_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_771_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
lean_inc(v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 1);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_770_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
v___x_761_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_742_, v_cache_752_, v_funext_753_, v___x_760_);
lean_dec_ref(v___x_760_);
lean_dec(v_a_742_);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_761_, 0);
lean_dec(v_unused_769_);
v___x_763_ = v___x_761_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_dec(v___x_761_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_a_755_);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_755_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_a_772_ = lean_ctor_get(v_r_754_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v_r_754_);
v___x_773_ = lean_box(0);
v___x_774_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_742_, v_cache_752_, v_funext_753_, v___x_773_);
lean_dec(v_a_742_);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_782_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 1);
lean_ctor_set(v___x_776_, 0, v_a_772_);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_772_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object* v_00_u03b1_783_, lean_object* v_k_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(v_00_u03b1_783_, v_k_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___redArg(lean_object* v_k_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_wellBehavedMethods_807_; 
v_wellBehavedMethods_807_ = lean_ctor_get_uint8(v_a_797_, sizeof(void*)*2);
if (v_wellBehavedMethods_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_cache_810_; lean_object* v_funext_811_; lean_object* v_r_812_; 
v___x_808_ = lean_st_ref_get(v_a_799_);
v___x_809_ = lean_st_ref_get(v_a_799_);
v_cache_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc_ref(v_cache_810_);
lean_dec(v___x_808_);
v_funext_811_ = lean_ctor_get(v___x_809_, 2);
lean_inc_ref(v_funext_811_);
lean_dec(v___x_809_);
lean_inc(v_a_799_);
v_r_812_ = lean_apply_10(v_k_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, lean_box(0));
if (lean_obj_tag(v_r_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_829_; 
v_a_813_ = lean_ctor_get(v_r_812_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_r_812_);
if (v_isSharedCheck_829_ == 0)
{
v___x_815_ = v_r_812_;
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v_r_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
lean_inc(v_a_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 1);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_828_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v___x_819_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_799_, v_cache_810_, v_funext_811_, v___x_818_);
lean_dec_ref(v___x_818_);
lean_dec(v_a_799_);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_819_, 0);
lean_dec(v_unused_827_);
v___x_821_ = v___x_819_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_dec(v___x_819_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_a_813_);
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_813_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_830_ = lean_ctor_get(v_r_812_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v_r_812_);
v___x_831_ = lean_box(0);
v___x_832_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_799_, v_cache_810_, v_funext_811_, v___x_831_);
lean_dec(v_a_799_);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_840_);
v___x_834_ = v___x_832_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___x_832_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 1);
lean_ctor_set(v___x_834_, 0, v_a_830_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_830_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_apply_10(v_k_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, lean_box(0));
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___redArg___boxed(lean_object* v_k_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___redArg(v_k_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved(lean_object* v_00_u03b1_854_, lean_object* v_k_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_wellBehavedMethods_866_; 
v_wellBehavedMethods_866_ = lean_ctor_get_uint8(v_a_856_, sizeof(void*)*2);
if (v_wellBehavedMethods_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_cache_869_; lean_object* v_funext_870_; lean_object* v_r_871_; 
v___x_867_ = lean_st_ref_get(v_a_858_);
v___x_868_ = lean_st_ref_get(v_a_858_);
v_cache_869_ = lean_ctor_get(v___x_867_, 1);
lean_inc_ref(v_cache_869_);
lean_dec(v___x_867_);
v_funext_870_ = lean_ctor_get(v___x_868_, 2);
lean_inc_ref(v_funext_870_);
lean_dec(v___x_868_);
lean_inc(v_a_858_);
v_r_871_ = lean_apply_10(v_k_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, lean_box(0));
if (lean_obj_tag(v_r_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_888_; 
v_a_872_ = lean_ctor_get(v_r_871_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_r_871_);
if (v_isSharedCheck_888_ == 0)
{
v___x_874_ = v_r_871_;
v_isShared_875_ = v_isSharedCheck_888_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v_r_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_888_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
lean_inc(v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 1);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_887_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v___x_878_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_858_, v_cache_869_, v_funext_870_, v___x_877_);
lean_dec_ref(v___x_877_);
lean_dec(v_a_858_);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_886_);
v___x_880_ = v___x_878_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_a_872_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_872_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_a_889_ = lean_ctor_get(v_r_871_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v_r_871_);
v___x_890_ = lean_box(0);
v___x_891_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_858_, v_cache_869_, v_funext_870_, v___x_890_);
lean_dec(v_a_858_);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_891_, 0);
lean_dec(v_unused_899_);
v___x_893_ = v___x_891_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_dec(v___x_891_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 1);
lean_ctor_set(v___x_893_, 0, v_a_889_);
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_889_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_apply_10(v_k_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, lean_box(0));
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved___boxed(lean_object* v_00_u03b1_901_, lean_object* v_k_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_Sym_Simp_withoutModifyingCacheIfNotWellBehaved(v_00_u03b1_901_, v_k_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp(lean_object* v_e_914_, lean_object* v_methods_915_, lean_object* v_config_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_924_, 0, v_e_914_);
v___x_925_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_924_, v_methods_915_, v_config_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object* v_e_926_, lean_object* v_methods_927_, lean_object* v_config_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Meta_Sym_simp(v_e_926_, v_methods_927_, v_config_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
return v_res_936_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed = _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed();
l_Lean_Meta_Sym_Simp_instInhabitedMethods_default = _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default);
l_Lean_Meta_Sym_Simp_instInhabitedMethods = _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedMethods);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
}
#ifdef __cplusplus
}
#endif
