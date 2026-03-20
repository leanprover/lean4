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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_Result_isContextDependent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isContextDependent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_done_8_; uint8_t v_contextDependent_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_done_8_ = lean_ctor_get_uint8(v_t_6_, 0);
v_contextDependent_9_ = lean_ctor_get_uint8(v_t_6_, 1);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_box(v_done_8_);
v___x_11_ = lean_box(v_contextDependent_9_);
v___x_12_ = lean_apply_2(v_k_7_, v___x_10_, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_e_x27_13_; lean_object* v_proof_14_; uint8_t v_done_15_; uint8_t v_contextDependent_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_e_x27_13_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_e_x27_13_);
v_proof_14_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_proof_14_);
v_done_15_ = lean_ctor_get_uint8(v_t_6_, sizeof(void*)*2);
v_contextDependent_16_ = lean_ctor_get_uint8(v_t_6_, sizeof(void*)*2 + 1);
lean_dec_ref(v_t_6_);
v___x_17_ = lean_box(v_done_15_);
v___x_18_ = lean_box(v_contextDependent_16_);
v___x_19_ = lean_apply_4(v_k_7_, v_e_x27_13_, v_proof_14_, v___x_17_, v___x_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___boxed(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Meta_Sym_Simp_Result_ctorElim(v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim___redArg(lean_object* v_t_32_, lean_object* v_rfl_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_32_, v_rfl_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_rfl_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_36_, v_rfl_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim___redArg(lean_object* v_t_40_, lean_object* v_step_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_40_, v_step_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_step_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_44_, v_step_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t v_done_52_, uint8_t v_contextDependent_53_){
_start:
{
if (v_done_52_ == 0)
{
if (v_contextDependent_53_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_54_, 0, v_contextDependent_53_);
lean_ctor_set_uint8(v___x_54_, 1, v_contextDependent_53_);
return v___x_54_;
}
else
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_55_, 0, v_done_52_);
lean_ctor_set_uint8(v___x_55_, 1, v_contextDependent_53_);
return v___x_55_;
}
}
else
{
if (v_contextDependent_53_ == 0)
{
lean_object* v___x_56_; 
v___x_56_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_56_, 0, v_done_52_);
lean_ctor_set_uint8(v___x_56_, 1, v_contextDependent_53_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_57_, 0, v_contextDependent_53_);
lean_ctor_set_uint8(v___x_57_, 1, v_contextDependent_53_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult___boxed(lean_object* v_done_58_, lean_object* v_contextDependent_59_){
_start:
{
uint8_t v_done_boxed_60_; uint8_t v_contextDependent_boxed_61_; lean_object* v_res_62_; 
v_done_boxed_60_ = lean_unbox(v_done_58_);
v_contextDependent_boxed_61_ = lean_unbox(v_contextDependent_59_);
v_res_62_ = l_Lean_Meta_Sym_Simp_mkRflResult(v_done_boxed_60_, v_contextDependent_boxed_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t v_contextDependent_63_){
_start:
{
if (v_contextDependent_63_ == 0)
{
lean_object* v___x_64_; 
v___x_64_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_64_, 0, v_contextDependent_63_);
lean_ctor_set_uint8(v___x_64_, 1, v_contextDependent_63_);
return v___x_64_;
}
else
{
uint8_t v___x_65_; lean_object* v___x_66_; 
v___x_65_ = 0;
v___x_66_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_66_, 0, v___x_65_);
lean_ctor_set_uint8(v___x_66_, 1, v_contextDependent_63_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD___boxed(lean_object* v_contextDependent_67_){
_start:
{
uint8_t v_contextDependent_boxed_68_; lean_object* v_res_69_; 
v_contextDependent_boxed_68_ = lean_unbox(v_contextDependent_67_);
v_res_69_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_boxed_68_);
return v_res_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_Result_isContextDependent(lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
uint8_t v_contextDependent_71_; 
v_contextDependent_71_ = lean_ctor_get_uint8(v_x_70_, 1);
return v_contextDependent_71_;
}
else
{
uint8_t v_contextDependent_72_; 
v_contextDependent_72_ = lean_ctor_get_uint8(v_x_70_, sizeof(void*)*2 + 1);
return v_contextDependent_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isContextDependent___boxed(lean_object* v_x_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Lean_Meta_Sym_Simp_Result_isContextDependent(v_x_73_);
lean_dec_ref(v_x_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
uint8_t v_done_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_done_77_ = lean_ctor_get_uint8(v_x_76_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v_x_76_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_dec(v_x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; lean_object* v___x_83_; 
v___x_81_ = 1;
if (v_isShared_80_ == 0)
{
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_84_, 0, v_done_77_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_ctor_set_uint8(v___x_83_, 1, v___x_81_);
return v___x_83_;
}
}
}
else
{
lean_object* v_e_x27_86_; lean_object* v_proof_87_; uint8_t v_done_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_e_x27_86_ = lean_ctor_get(v_x_76_, 0);
v_proof_87_ = lean_ctor_get(v_x_76_, 1);
v_done_88_ = lean_ctor_get_uint8(v_x_76_, sizeof(void*)*2);
v_isSharedCheck_96_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v_x_76_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_proof_87_);
lean_inc(v_e_x27_86_);
lean_dec(v_x_76_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint8_t v___x_92_; lean_object* v___x_94_; 
v___x_92_ = 1;
if (v_isShared_91_ == 0)
{
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_e_x27_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_proof_87_);
lean_ctor_set_uint8(v_reuseFailAlloc_95_, sizeof(void*)*2, v_done_88_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*2 + 1, v___x_92_);
return v___x_94_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_box(0);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0);
v___x_100_ = l_ReaderT_instMonad___redArg(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6(void){
_start:
{
lean_object* v___x_105_; lean_object* v___f_106_; 
v___x_105_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_106_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_106_, 0, v___x_105_);
return v___f_106_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7(void){
_start:
{
lean_object* v___x_107_; lean_object* v___f_108_; 
v___x_107_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_108_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_108_, 0, v___x_107_);
return v___f_108_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8(void){
_start:
{
lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___x_111_; 
v___f_109_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7);
v___f_110_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___f_110_);
lean_ctor_set(v___x_111_, 1, v___f_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9(void){
_start:
{
lean_object* v___x_112_; lean_object* v___f_113_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_113_, 0, v___x_112_);
return v___f_113_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10(void){
_start:
{
lean_object* v___x_114_; lean_object* v___f_115_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8);
v___f_115_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_115_, 0, v___x_114_);
return v___f_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11(void){
_start:
{
lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_118_; 
v___f_116_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10);
v___f_117_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___f_117_);
lean_ctor_set(v___x_118_, 1, v___f_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12(void){
_start:
{
lean_object* v___x_119_; lean_object* v___f_120_; 
v___x_119_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11);
v___f_120_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_120_, 0, v___x_119_);
return v___f_120_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13(void){
_start:
{
lean_object* v___x_121_; lean_object* v___f_122_; 
v___x_121_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11);
v___f_122_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_122_, 0, v___x_121_);
return v___f_122_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14(void){
_start:
{
lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; 
v___f_123_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13);
v___f_124_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___f_124_);
lean_ctor_set(v___x_125_, 1, v___f_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15(void){
_start:
{
lean_object* v___x_126_; lean_object* v___f_127_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14);
v___f_127_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_127_, 0, v___x_126_);
return v___f_127_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16(void){
_start:
{
lean_object* v___x_128_; lean_object* v___f_129_; 
v___x_128_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14);
v___f_129_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_129_, 0, v___x_128_);
return v___f_129_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17(void){
_start:
{
lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v___f_130_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16);
v___f_131_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___f_131_);
lean_ctor_set(v___x_132_, 1, v___f_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18(void){
_start:
{
lean_object* v___x_133_; lean_object* v___f_134_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17);
v___f_134_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_134_, 0, v___x_133_);
return v___f_134_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19(void){
_start:
{
lean_object* v___x_135_; lean_object* v___f_136_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17);
v___f_136_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
return v___f_136_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20(void){
_start:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v___f_137_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19);
v___f_138_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___f_138_);
lean_ctor_set(v___x_139_, 1, v___f_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21(void){
_start:
{
lean_object* v___x_140_; lean_object* v___f_141_; 
v___x_140_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_141_, 0, v___x_140_);
return v___f_141_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22(void){
_start:
{
lean_object* v___x_142_; lean_object* v___f_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_143_, 0, v___x_142_);
return v___f_143_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23(void){
_start:
{
lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v___f_144_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22);
v___f_145_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_145_);
lean_ctor_set(v___x_146_, 1, v___f_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24(void){
_start:
{
lean_object* v___x_147_; lean_object* v___f_148_; 
v___x_147_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_148_, 0, v___x_147_);
return v___f_148_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25(void){
_start:
{
lean_object* v___x_149_; lean_object* v___f_150_; 
v___x_149_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23);
v___f_150_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_150_, 0, v___x_149_);
return v___f_150_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26(void){
_start:
{
lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_153_; 
v___f_151_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25);
v___f_152_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___f_152_);
lean_ctor_set(v___x_153_, 1, v___f_151_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; 
v___x_157_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_158_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_159_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_160_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_159_, v___x_158_, v___x_157_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31(void){
_start:
{
lean_object* v___x_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30);
v___f_162_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_163_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_164_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_163_, v___f_162_, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___f_167_; lean_object* v___x_168_; 
v___x_165_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31);
v___x_166_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_167_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_168_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_167_, v___x_166_, v___x_165_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33(void){
_start:
{
lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_172_; 
v___x_169_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32);
v___f_170_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_171_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_172_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_171_, v___f_170_, v___x_169_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33);
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_175_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_176_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_175_, v___x_174_, v___x_173_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35(void){
_start:
{
lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; 
v___x_177_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34);
v___f_178_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_179_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_180_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_179_, v___f_178_, v___x_177_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36(void){
_start:
{
lean_object* v___x_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35);
v___f_182_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_183_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_184_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_183_, v___f_182_, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___f_187_; 
v___x_185_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___x_186_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_187_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_187_, 0, v___x_186_);
lean_closure_set(v___f_187_, 1, v___x_185_);
return v___f_187_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38(void){
_start:
{
lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; 
v___f_188_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_189_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_190_, 0, v___f_189_);
lean_closure_set(v___f_190_, 1, v___f_188_);
return v___f_190_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39(void){
_start:
{
lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___f_193_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___f_192_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_193_, 0, v___f_192_);
lean_closure_set(v___f_193_, 1, v___x_191_);
return v___f_193_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40(void){
_start:
{
lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; 
v___f_194_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_195_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39);
v___f_196_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_196_, 0, v___f_195_);
lean_closure_set(v___f_196_, 1, v___f_194_);
return v___f_196_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41(void){
_start:
{
lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; 
v___f_197_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_198_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40);
v___f_199_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_199_, 0, v___f_198_);
lean_closure_set(v___f_199_, 1, v___f_197_);
return v___f_199_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object* v_00_u03b1_203_){
_start:
{
lean_object* v___x_204_; lean_object* v_toApplicative_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_275_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1);
v_toApplicative_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v___x_204_, 1);
lean_dec(v_unused_276_);
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_275_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_toApplicative_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_275_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_toFunctor_209_; lean_object* v_toSeq_210_; lean_object* v_toSeqLeft_211_; lean_object* v_toSeqRight_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_273_; 
v_toFunctor_209_ = lean_ctor_get(v_toApplicative_205_, 0);
v_toSeq_210_ = lean_ctor_get(v_toApplicative_205_, 2);
v_toSeqLeft_211_ = lean_ctor_get(v_toApplicative_205_, 3);
v_toSeqRight_212_ = lean_ctor_get(v_toApplicative_205_, 4);
v_isSharedCheck_273_ = !lean_is_exclusive(v_toApplicative_205_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_toApplicative_205_, 1);
lean_dec(v_unused_274_);
v___x_214_ = v_toApplicative_205_;
v_isShared_215_ = v_isSharedCheck_273_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_toSeqRight_212_);
lean_inc(v_toSeqLeft_211_);
lean_inc(v_toSeq_210_);
lean_inc(v_toFunctor_209_);
lean_dec(v_toApplicative_205_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_273_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_225_; 
v___f_216_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2));
v___f_217_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3));
lean_inc_ref(v_toFunctor_209_);
v___f_218_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_218_, 0, v_toFunctor_209_);
v___f_219_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_219_, 0, v_toFunctor_209_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___f_218_);
lean_ctor_set(v___x_220_, 1, v___f_219_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_221_, 0, v_toSeqRight_212_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_222_, 0, v_toSeqLeft_211_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_223_, 0, v_toSeq_210_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v___f_221_);
lean_ctor_set(v___x_214_, 3, v___f_222_);
lean_ctor_set(v___x_214_, 2, v___f_223_);
lean_ctor_set(v___x_214_, 1, v___f_216_);
lean_ctor_set(v___x_214_, 0, v___x_220_);
v___x_225_ = v___x_214_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___f_216_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v___f_222_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v___f_221_);
v___x_225_ = v_reuseFailAlloc_272_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v___f_217_);
lean_ctor_set(v___x_207_, 0, v___x_225_);
v___x_227_ = v___x_207_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___f_217_);
v___x_227_ = v_reuseFailAlloc_271_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v_toApplicative_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_269_; 
v___x_228_ = l_ReaderT_instMonad___redArg(v___x_227_);
v_toApplicative_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v___x_228_, 1);
lean_dec(v_unused_270_);
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_269_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_toApplicative_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_269_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_toFunctor_233_; lean_object* v_toSeq_234_; lean_object* v_toSeqLeft_235_; lean_object* v_toSeqRight_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_267_; 
v_toFunctor_233_ = lean_ctor_get(v_toApplicative_229_, 0);
v_toSeq_234_ = lean_ctor_get(v_toApplicative_229_, 2);
v_toSeqLeft_235_ = lean_ctor_get(v_toApplicative_229_, 3);
v_toSeqRight_236_ = lean_ctor_get(v_toApplicative_229_, 4);
v_isSharedCheck_267_ = !lean_is_exclusive(v_toApplicative_229_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_dec(v_unused_268_);
v___x_238_ = v_toApplicative_229_;
v_isShared_239_ = v_isSharedCheck_267_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toSeqRight_236_);
lean_inc(v_toSeqLeft_235_);
lean_inc(v_toSeq_234_);
lean_inc(v_toFunctor_233_);
lean_dec(v_toApplicative_229_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_267_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___f_240_; lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_249_; 
v___f_240_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4));
v___f_241_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5));
lean_inc_ref(v_toFunctor_233_);
v___f_242_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_242_, 0, v_toFunctor_233_);
v___f_243_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_243_, 0, v_toFunctor_233_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___f_242_);
lean_ctor_set(v___x_244_, 1, v___f_243_);
v___f_245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_245_, 0, v_toSeqRight_236_);
v___f_246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_246_, 0, v_toSeqLeft_235_);
v___f_247_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_247_, 0, v_toSeq_234_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 4, v___f_245_);
lean_ctor_set(v___x_238_, 3, v___f_246_);
lean_ctor_set(v___x_238_, 2, v___f_247_);
lean_ctor_set(v___x_238_, 1, v___f_240_);
lean_ctor_set(v___x_238_, 0, v___x_244_);
v___x_249_ = v___x_238_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___f_240_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v___f_247_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v___f_246_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v___f_245_);
v___x_249_ = v_reuseFailAlloc_266_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_251_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___f_241_);
lean_ctor_set(v___x_231_, 0, v___x_249_);
v___x_251_ = v___x_231_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___f_241_);
v___x_251_ = v_reuseFailAlloc_265_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_toMonadRef_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_252_ = l_ReaderT_instMonad___redArg(v___x_251_);
v___x_253_ = l_ReaderT_instMonad___redArg(v___x_252_);
v___x_254_ = l_ReaderT_instMonad___redArg(v___x_253_);
v___x_255_ = l_ReaderT_instMonad___redArg(v___x_254_);
v___x_256_ = l_ReaderT_instMonad___redArg(v___x_255_);
v___x_257_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26);
v___x_258_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36);
v_toMonadRef_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_toMonadRef_259_);
v___f_260_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41);
lean_inc_ref(v___x_256_);
v___x_261_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_260_, v___x_256_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_257_);
lean_ctor_set(v___x_262_, 1, v_toMonadRef_259_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43);
v___x_264_ = l_Lean_throwError___redArg(v___x_256_, v___x_262_, v___x_263_);
return v___x_264_;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(lean_object* v_msgData_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; lean_object* v_env_284_; lean_object* v___x_285_; lean_object* v_mctx_286_; lean_object* v_lctx_287_; lean_object* v_options_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_283_ = lean_st_ref_get(v___y_281_);
v_env_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc_ref(v_env_284_);
lean_dec(v___x_283_);
v___x_285_ = lean_st_ref_get(v___y_279_);
v_mctx_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref(v_mctx_286_);
lean_dec(v___x_285_);
v_lctx_287_ = lean_ctor_get(v___y_278_, 2);
v_options_288_ = lean_ctor_get(v___y_280_, 2);
lean_inc_ref(v_options_288_);
lean_inc_ref(v_lctx_287_);
v___x_289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_289_, 0, v_env_284_);
lean_ctor_set(v___x_289_, 1, v_mctx_286_);
lean_ctor_set(v___x_289_, 2, v_lctx_287_);
lean_ctor_set(v___x_289_, 3, v_options_288_);
v___x_290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_msgData_277_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0___boxed(lean_object* v_msgData_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msgData_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_ref_305_; lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
v_ref_305_ = lean_ctor_get(v___y_302_, 5);
v___x_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msg_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_inc(v_ref_305_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_ref_305_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 1);
lean_ctor_set(v___x_309_, 0, v___x_311_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg___boxed(lean_object* v_msg_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43);
v___x_335_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v___x_334_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v_x_336_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1(void){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; 
v___f_349_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0));
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___f_349_);
lean_ctor_set(v___x_350_, 1, v___f_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default(void){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(lean_object* v_00_u03b1_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_353_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(v_00_u03b1_365_, v_msg_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
return v_res_377_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default;
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object* v_m_379_){
_start:
{
lean_inc_ref(v_m_379_);
return v_m_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_380_);
lean_dec_ref(v_m_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object* v_m_382_){
_start:
{
lean_inc(v_m_382_);
return v_m_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_383_);
lean_dec(v_m_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_a_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_a_391_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_412_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object* v_x_416_, lean_object* v_methods_417_, lean_object* v_config_418_, lean_object* v_s_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_lctx_427_; lean_object* v_decls_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_469_; 
v_lctx_427_ = lean_ctor_get(v_a_422_, 2);
lean_inc_ref(v_lctx_427_);
v_decls_428_ = lean_ctor_get(v_lctx_427_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_lctx_427_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_470_ = lean_ctor_get(v_lctx_427_, 2);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_lctx_427_, 0);
lean_dec(v_unused_471_);
v___x_430_ = v_lctx_427_;
v_isShared_431_ = v_isSharedCheck_469_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_decls_428_);
lean_dec(v_lctx_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_469_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_size_432_; lean_object* v_persistentCache_433_; lean_object* v_funext_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_466_; 
v_size_432_ = lean_ctor_get(v_decls_428_, 2);
lean_inc(v_size_432_);
lean_dec_ref(v_decls_428_);
v_persistentCache_433_ = lean_ctor_get(v_s_419_, 1);
v_funext_434_ = lean_ctor_get(v_s_419_, 3);
v_isSharedCheck_466_ = !lean_is_exclusive(v_s_419_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_s_419_, 2);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_s_419_, 0);
lean_dec(v_unused_468_);
v___x_436_ = v_s_419_;
v_isShared_437_ = v_isSharedCheck_466_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_funext_434_);
lean_inc(v_persistentCache_433_);
lean_dec(v_s_419_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_466_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = lean_unsigned_to_nat(0u);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 2, v___x_438_);
lean_ctor_set(v___x_430_, 1, v_size_432_);
lean_ctor_set(v___x_430_, 0, v_config_418_);
v___x_440_ = v___x_430_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_config_418_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_size_432_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v___x_438_);
v___x_440_ = v_reuseFailAlloc_465_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 2, v___x_441_);
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_443_ = v___x_436_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_persistentCache_433_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_funext_434_);
v___x_443_ = v_reuseFailAlloc_464_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_st_mk_ref(v___x_443_);
lean_inc(v___x_444_);
v___x_445_ = lean_apply_10(v_x_416_, v_methods_417_, v___x_440_, v___x_444_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, lean_box(0));
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_455_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = lean_st_ref_get(v___x_444_);
lean_dec(v___x_444_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_a_446_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec(v___x_444_);
v_a_456_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_445_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_445_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object* v_x_472_, lean_object* v_methods_473_, lean_object* v_config_474_, lean_object* v_s_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_472_, v_methods_473_, v_config_474_, v_s_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object* v_00_u03b1_484_, lean_object* v_x_485_, lean_object* v_methods_486_, lean_object* v_config_487_, lean_object* v_s_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_485_, v_methods_486_, v_config_487_, v_s_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object* v_00_u03b1_497_, lean_object* v_x_498_, lean_object* v_methods_499_, lean_object* v_config_500_, lean_object* v_s_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_Sym_Simp_SimpM_run(v_00_u03b1_497_, v_x_498_, v_methods_499_, v_config_500_, v_s_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_510_);
lean_ctor_set(v___x_512_, 3, v___x_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object* v_x_513_, lean_object* v_methods_514_, lean_object* v_config_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_lctx_523_; lean_object* v_decls_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_545_; 
v_lctx_523_ = lean_ctor_get(v_a_518_, 2);
lean_inc_ref(v_lctx_523_);
v_decls_524_ = lean_ctor_get(v_lctx_523_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_lctx_523_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_lctx_523_, 2);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_lctx_523_, 0);
lean_dec(v_unused_547_);
v___x_526_ = v_lctx_523_;
v_isShared_527_ = v_isSharedCheck_545_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_decls_524_);
lean_dec(v_lctx_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_545_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_size_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v_size_528_ = lean_ctor_get(v_decls_524_, 2);
lean_inc(v_size_528_);
lean_dec_ref(v_decls_524_);
v___x_529_ = lean_unsigned_to_nat(0u);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_529_);
lean_ctor_set(v___x_526_, 1, v_size_528_);
lean_ctor_set(v___x_526_, 0, v_config_515_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_config_515_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_size_528_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v___x_529_);
v___x_531_ = v_reuseFailAlloc_544_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0);
v___x_533_ = lean_st_mk_ref(v___x_532_);
lean_inc(v___x_533_);
v___x_534_ = lean_apply_10(v_x_513_, v_methods_514_, v___x_531_, v___x_533_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, lean_box(0));
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = lean_st_ref_get(v___x_533_);
lean_dec(v___x_533_);
lean_dec(v___x_539_);
if (v_isShared_538_ == 0)
{
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_535_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
else
{
lean_dec(v___x_533_);
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object* v_x_548_, lean_object* v_methods_549_, lean_object* v_config_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_548_, v_methods_549_, v_config_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object* v_00_u03b1_559_, lean_object* v_x_560_, lean_object* v_methods_561_, lean_object* v_config_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_560_, v_methods_561_, v_config_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object* v_00_u03b1_571_, lean_object* v_x_572_, lean_object* v_methods_573_, lean_object* v_config_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(v_00_u03b1_571_, v_x_572_, v_methods_573_, v_config_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object* v_a_00___x40___internal___hyg_594_, lean_object* v_a_00___x40___internal___hyg_595_, lean_object* v_a_00___x40___internal___hyg_596_, lean_object* v_a_00___x40___internal___hyg_597_, lean_object* v_a_00___x40___internal___hyg_598_, lean_object* v_a_00___x40___internal___hyg_599_, lean_object* v_a_00___x40___internal___hyg_600_, lean_object* v_a_00___x40___internal___hyg_601_, lean_object* v_a_00___x40___internal___hyg_602_, lean_object* v_a_00___x40___internal___hyg_603_, lean_object* v_a_00___x40___internal___hyg_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = lean_sym_simp(v_a_00___x40___internal___hyg_594_, v_a_00___x40___internal___hyg_595_, v_a_00___x40___internal___hyg_596_, v_a_00___x40___internal___hyg_597_, v_a_00___x40___internal___hyg_598_, v_a_00___x40___internal___hyg_599_, v_a_00___x40___internal___hyg_600_, v_a_00___x40___internal___hyg_601_, v_a_00___x40___internal___hyg_602_, v_a_00___x40___internal___hyg_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object* v_a_606_){
_start:
{
lean_object* v_config_608_; lean_object* v___x_609_; 
v_config_608_ = lean_ctor_get(v_a_606_, 0);
lean_inc_ref(v_config_608_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_config_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_610_);
lean_dec_ref(v_a_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_614_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_pre_646_; lean_object* v___x_647_; 
v_pre_646_ = lean_ctor_get(v_a_636_, 0);
lean_inc_ref(v_pre_646_);
v___x_647_ = lean_apply_11(v_pre_646_, v_e_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_Sym_Simp_pre(v_e_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object* v_e_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_post_671_; lean_object* v___x_672_; 
v_post_671_ = lean_ctor_get(v_a_661_, 1);
lean_inc_ref(v_post_671_);
v___x_672_ = lean_apply_11(v_post_671_, v_e_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, lean_box(0));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object* v_e_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Meta_Sym_Simp_post(v_e_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object* v_a_685_, lean_object* v_persistentCache_686_, lean_object* v_transientCache_687_, lean_object* v_funext_688_, lean_object* v_a_x3f_689_){
_start:
{
lean_object* v___x_691_; lean_object* v_numSteps_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
v___x_691_ = lean_st_ref_take(v_a_685_);
v_numSteps_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_703_ = lean_ctor_get(v___x_691_, 3);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v___x_691_, 2);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v___x_691_, 1);
lean_dec(v_unused_705_);
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_numSteps_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 3, v_funext_688_);
lean_ctor_set(v___x_694_, 2, v_transientCache_687_);
lean_ctor_set(v___x_694_, 1, v_persistentCache_686_);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_numSteps_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_persistentCache_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_transientCache_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_funext_688_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_st_ref_set(v_a_685_, v___x_697_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object* v_a_706_, lean_object* v_persistentCache_707_, lean_object* v_transientCache_708_, lean_object* v_funext_709_, lean_object* v_a_x3f_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_706_, v_persistentCache_707_, v_transientCache_708_, v_funext_709_, v_a_x3f_710_);
lean_dec(v_a_x3f_710_);
lean_dec(v_a_706_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object* v_k_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_persistentCache_727_; lean_object* v_transientCache_728_; lean_object* v_funext_729_; lean_object* v_r_730_; 
v___x_724_ = lean_st_ref_get(v_a_716_);
v___x_725_ = lean_st_ref_get(v_a_716_);
v___x_726_ = lean_st_ref_get(v_a_716_);
v_persistentCache_727_ = lean_ctor_get(v___x_724_, 1);
lean_inc_ref(v_persistentCache_727_);
lean_dec(v___x_724_);
v_transientCache_728_ = lean_ctor_get(v___x_725_, 2);
lean_inc_ref(v_transientCache_728_);
lean_dec(v___x_725_);
v_funext_729_ = lean_ctor_get(v___x_726_, 3);
lean_inc_ref(v_funext_729_);
lean_dec(v___x_726_);
lean_inc(v_a_716_);
v_r_730_ = lean_apply_10(v_k_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, lean_box(0));
if (lean_obj_tag(v_r_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_747_; 
v_a_731_ = lean_ctor_get(v_r_730_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_r_730_);
if (v_isSharedCheck_747_ == 0)
{
v___x_733_ = v_r_730_;
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v_r_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
lean_inc(v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 1);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_746_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v___x_737_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_716_, v_persistentCache_727_, v_transientCache_728_, v_funext_729_, v___x_736_);
lean_dec_ref(v___x_736_);
lean_dec(v_a_716_);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v___x_737_, 0);
lean_dec(v_unused_745_);
v___x_739_ = v___x_737_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_dec(v___x_737_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v_a_731_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_731_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_748_ = lean_ctor_get(v_r_730_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v_r_730_);
v___x_749_ = lean_box(0);
v___x_750_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_716_, v_persistentCache_727_, v_transientCache_728_, v_funext_729_, v___x_749_);
lean_dec(v_a_716_);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_758_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 0, v_a_748_);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_748_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object* v_k_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object* v_00_u03b1_771_, lean_object* v_k_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_persistentCache_786_; lean_object* v_transientCache_787_; lean_object* v_funext_788_; lean_object* v_r_789_; 
v___x_783_ = lean_st_ref_get(v_a_775_);
v___x_784_ = lean_st_ref_get(v_a_775_);
v___x_785_ = lean_st_ref_get(v_a_775_);
v_persistentCache_786_ = lean_ctor_get(v___x_783_, 1);
lean_inc_ref(v_persistentCache_786_);
lean_dec(v___x_783_);
v_transientCache_787_ = lean_ctor_get(v___x_784_, 2);
lean_inc_ref(v_transientCache_787_);
lean_dec(v___x_784_);
v_funext_788_ = lean_ctor_get(v___x_785_, 3);
lean_inc_ref(v_funext_788_);
lean_dec(v___x_785_);
lean_inc(v_a_775_);
v_r_789_ = lean_apply_10(v_k_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, lean_box(0));
if (lean_obj_tag(v_r_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_a_790_ = lean_ctor_get(v_r_789_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_r_789_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v_r_789_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v_r_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
lean_inc(v_a_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_805_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v___x_796_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_775_, v_persistentCache_786_, v_transientCache_787_, v_funext_788_, v___x_795_);
lean_dec_ref(v___x_795_);
lean_dec(v_a_775_);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_804_);
v___x_798_ = v___x_796_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_dec(v___x_796_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_a_790_);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_790_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
v_a_807_ = lean_ctor_get(v_r_789_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v_r_789_);
v___x_808_ = lean_box(0);
v___x_809_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_775_, v_persistentCache_786_, v_transientCache_787_, v_funext_788_, v___x_808_);
lean_dec(v_a_775_);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_809_, 0);
lean_dec(v_unused_817_);
v___x_811_ = v___x_809_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_dec(v___x_809_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 1);
lean_ctor_set(v___x_811_, 0, v_a_807_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_807_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object* v_00_u03b1_818_, lean_object* v_k_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(v_00_u03b1_818_, v_k_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(lean_object* v_a_831_, lean_object* v_transientCache_832_, lean_object* v_funext_833_, lean_object* v_a_x3f_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_numSteps_837_; lean_object* v_persistentCache_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_848_; 
v___x_836_ = lean_st_ref_take(v_a_831_);
v_numSteps_837_ = lean_ctor_get(v___x_836_, 0);
v_persistentCache_838_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_849_ = lean_ctor_get(v___x_836_, 3);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v___x_836_, 2);
lean_dec(v_unused_850_);
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_persistentCache_838_);
lean_inc(v_numSteps_837_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 3, v_funext_833_);
lean_ctor_set(v___x_840_, 2, v_transientCache_832_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_numSteps_837_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_persistentCache_838_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_transientCache_832_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v_funext_833_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_st_ref_set(v_a_831_, v___x_843_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(lean_object* v_a_851_, lean_object* v_transientCache_852_, lean_object* v_funext_853_, lean_object* v_a_x3f_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_851_, v_transientCache_852_, v_funext_853_, v_a_x3f_854_);
lean_dec(v_a_x3f_854_);
lean_dec(v_a_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(lean_object* v_k_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_transientCache_870_; lean_object* v_funext_871_; lean_object* v_r_872_; 
v___x_868_ = lean_st_ref_get(v_a_860_);
v___x_869_ = lean_st_ref_get(v_a_860_);
v_transientCache_870_ = lean_ctor_get(v___x_868_, 2);
lean_inc_ref(v_transientCache_870_);
lean_dec(v___x_868_);
v_funext_871_ = lean_ctor_get(v___x_869_, 3);
lean_inc_ref(v_funext_871_);
lean_dec(v___x_869_);
lean_inc(v_a_860_);
v_r_872_ = lean_apply_10(v_k_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, lean_box(0));
if (lean_obj_tag(v_r_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_889_; 
v_a_873_ = lean_ctor_get(v_r_872_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_r_872_);
if (v_isSharedCheck_889_ == 0)
{
v___x_875_ = v_r_872_;
v_isShared_876_ = v_isSharedCheck_889_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_r_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_889_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
lean_inc(v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_888_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v___x_879_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_860_, v_transientCache_870_, v_funext_871_, v___x_878_);
lean_dec_ref(v___x_878_);
lean_dec(v_a_860_);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_879_, 0);
lean_dec(v_unused_887_);
v___x_881_ = v___x_879_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_879_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_a_873_);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_873_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_890_ = lean_ctor_get(v_r_872_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v_r_872_);
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_860_, v_transientCache_870_, v_funext_871_, v___x_891_);
lean_dec(v_a_860_);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_900_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v_a_890_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_890_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(lean_object* v_k_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(v_k_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_object* v_00_u03b1_913_, lean_object* v_k_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_transientCache_927_; lean_object* v_funext_928_; lean_object* v_r_929_; 
v___x_925_ = lean_st_ref_get(v_a_917_);
v___x_926_ = lean_st_ref_get(v_a_917_);
v_transientCache_927_ = lean_ctor_get(v___x_925_, 2);
lean_inc_ref(v_transientCache_927_);
lean_dec(v___x_925_);
v_funext_928_ = lean_ctor_get(v___x_926_, 3);
lean_inc_ref(v_funext_928_);
lean_dec(v___x_926_);
lean_inc(v_a_917_);
v_r_929_ = lean_apply_10(v_k_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, lean_box(0));
if (lean_obj_tag(v_r_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_946_; 
v_a_930_ = lean_ctor_get(v_r_929_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_r_929_);
if (v_isSharedCheck_946_ == 0)
{
v___x_932_ = v_r_929_;
v_isShared_933_ = v_isSharedCheck_946_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v_r_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_946_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
lean_inc(v_a_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 1);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_945_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v___x_936_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_917_, v_transientCache_927_, v_funext_928_, v___x_935_);
lean_dec_ref(v___x_935_);
lean_dec(v_a_917_);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_936_, 0);
lean_dec(v_unused_944_);
v___x_938_ = v___x_936_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_dec(v___x_936_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_a_930_);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_930_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_947_ = lean_ctor_get(v_r_929_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v_r_929_);
v___x_948_ = lean_box(0);
v___x_949_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_917_, v_transientCache_927_, v_funext_928_, v___x_948_);
lean_dec(v_a_917_);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_949_, 0);
lean_dec(v_unused_957_);
v___x_951_ = v___x_949_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_dec(v___x_949_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 1);
lean_ctor_set(v___x_951_, 0, v_a_947_);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_947_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(lean_object* v_00_u03b1_958_, lean_object* v_k_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(v_00_u03b1_958_, v_k_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp(lean_object* v_e_971_, lean_object* v_methods_972_, lean_object* v_config_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_981_, 0, v_e_971_);
v___x_982_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_981_, v_methods_972_, v_config_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object* v_e_983_, lean_object* v_methods_984_, lean_object* v_config_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Meta_Sym_simp(v_e_983_, v_methods_984_, v_config_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v_res_993_;
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
