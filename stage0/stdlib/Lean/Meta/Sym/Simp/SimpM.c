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
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value;
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
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_value;
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
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42;
static const lean_string_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<default>"};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value),((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx(lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(0u);
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(1u);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Sym_Simp_Result_ctorIdx(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
if (lean_obj_tag(v_t_10_) == 0)
{
uint8_t v_done_12_; uint8_t v_contextDependent_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_done_12_ = lean_ctor_get_uint8(v_t_10_, 0);
v_contextDependent_13_ = lean_ctor_get_uint8(v_t_10_, 1);
lean_dec_ref(v_t_10_);
v___x_14_ = lean_box(v_done_12_);
v___x_15_ = lean_box(v_contextDependent_13_);
v___x_16_ = lean_apply_2(v_k_11_, v___x_14_, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v_e_x27_17_; lean_object* v_proof_18_; uint8_t v_done_19_; uint8_t v_contextDependent_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_e_x27_17_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_e_x27_17_);
v_proof_18_ = lean_ctor_get(v_t_10_, 1);
lean_inc_ref(v_proof_18_);
v_done_19_ = lean_ctor_get_uint8(v_t_10_, sizeof(void*)*2);
v_contextDependent_20_ = lean_ctor_get_uint8(v_t_10_, sizeof(void*)*2 + 1);
lean_dec_ref(v_t_10_);
v___x_21_ = lean_box(v_done_19_);
v___x_22_ = lean_box(v_contextDependent_20_);
v___x_23_ = lean_apply_4(v_k_11_, v_e_x27_17_, v_proof_18_, v___x_21_, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorElim___boxed(lean_object* v_motive_30_, lean_object* v_ctorIdx_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_k_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_Sym_Simp_Result_ctorElim(v_motive_30_, v_ctorIdx_31_, v_t_32_, v_h_33_, v_k_34_);
lean_dec(v_ctorIdx_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim___redArg(lean_object* v_t_36_, lean_object* v_rfl_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_36_, v_rfl_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_rfl_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_rfl_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_40_, v_rfl_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim___redArg(lean_object* v_t_44_, lean_object* v_step_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_44_, v_step_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_step_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_step_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_48_, v_step_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t v_done_56_, uint8_t v_contextDependent_57_){
_start:
{
if (v_done_56_ == 0)
{
if (v_contextDependent_57_ == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_58_, 0, v_contextDependent_57_);
lean_ctor_set_uint8(v___x_58_, 1, v_contextDependent_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; 
v___x_59_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_59_, 0, v_done_56_);
lean_ctor_set_uint8(v___x_59_, 1, v_contextDependent_57_);
return v___x_59_;
}
}
else
{
if (v_contextDependent_57_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_60_, 0, v_done_56_);
lean_ctor_set_uint8(v___x_60_, 1, v_contextDependent_57_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_61_, 0, v_contextDependent_57_);
lean_ctor_set_uint8(v___x_61_, 1, v_contextDependent_57_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult___boxed(lean_object* v_done_62_, lean_object* v_contextDependent_63_){
_start:
{
uint8_t v_done_boxed_64_; uint8_t v_contextDependent_boxed_65_; lean_object* v_res_66_; 
v_done_boxed_64_ = lean_unbox(v_done_62_);
v_contextDependent_boxed_65_ = lean_unbox(v_contextDependent_63_);
v_res_66_ = l_Lean_Meta_Sym_Simp_mkRflResult(v_done_boxed_64_, v_contextDependent_boxed_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t v_contextDependent_67_){
_start:
{
if (v_contextDependent_67_ == 0)
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_68_, 0, v_contextDependent_67_);
lean_ctor_set_uint8(v___x_68_, 1, v_contextDependent_67_);
return v___x_68_;
}
else
{
uint8_t v___x_69_; lean_object* v___x_70_; 
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_70_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_70_, 1, v_contextDependent_67_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD___boxed(lean_object* v_contextDependent_71_){
_start:
{
uint8_t v_contextDependent_boxed_72_; lean_object* v_res_73_; 
v_contextDependent_boxed_72_ = lean_unbox(v_contextDependent_71_);
v_res_73_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_boxed_72_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_Result_isContextDependent(lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
uint8_t v_contextDependent_75_; 
v_contextDependent_75_ = lean_ctor_get_uint8(v_x_74_, 1);
return v_contextDependent_75_;
}
else
{
uint8_t v_contextDependent_76_; 
v_contextDependent_76_ = lean_ctor_get_uint8(v_x_74_, sizeof(void*)*2 + 1);
return v_contextDependent_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isContextDependent___boxed(lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Meta_Sym_Simp_Result_isContextDependent(v_x_77_);
lean_dec_ref(v_x_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
uint8_t v_done_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_89_; 
v_done_81_ = lean_ctor_get_uint8(v_x_80_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_89_ == 0)
{
v___x_83_ = v_x_80_;
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
uint8_t v___x_85_; lean_object* v___x_87_; 
v___x_85_ = 1;
if (v_isShared_84_ == 0)
{
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, 0, v_done_81_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_ctor_set_uint8(v___x_87_, 1, v___x_85_);
return v___x_87_;
}
}
}
else
{
lean_object* v_e_x27_90_; lean_object* v_proof_91_; uint8_t v_done_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_e_x27_90_ = lean_ctor_get(v_x_80_, 0);
v_proof_91_ = lean_ctor_get(v_x_80_, 1);
v_done_92_ = lean_ctor_get_uint8(v_x_80_, sizeof(void*)*2);
v_isSharedCheck_100_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v_x_80_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_proof_91_);
lean_inc(v_e_x27_90_);
lean_dec(v_x_80_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
uint8_t v___x_96_; lean_object* v___x_98_; 
v___x_96_ = 1;
if (v_isShared_95_ == 0)
{
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_e_x27_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_proof_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_99_, sizeof(void*)*2, v_done_92_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*2 + 1, v___x_96_);
return v___x_98_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(0);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_instMonadEIO(lean_box(0));
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0);
v___x_104_ = l_StateRefT_x27_instMonad___redArg(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6(void){
_start:
{
lean_object* v___x_109_; lean_object* v___f_110_; 
v___x_109_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_110_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_110_, 0, v___x_109_);
return v___f_110_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_112_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8(void){
_start:
{
lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v___f_113_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7);
v___f_114_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___f_114_);
lean_ctor_set(v___x_115_, 1, v___f_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9(void){
_start:
{
lean_object* v___x_116_; lean_object* v___f_117_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_117_, 0, v___x_116_);
return v___f_117_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10(void){
_start:
{
lean_object* v___x_118_; lean_object* v___f_119_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8);
v___f_119_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_119_, 0, v___x_118_);
return v___f_119_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11(void){
_start:
{
lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_120_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10);
v___f_121_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___f_121_);
lean_ctor_set(v___x_122_, 1, v___f_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12(void){
_start:
{
lean_object* v___x_123_; lean_object* v___f_124_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11);
v___f_124_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_124_, 0, v___x_123_);
return v___f_124_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13(void){
_start:
{
lean_object* v___x_125_; lean_object* v___f_126_; 
v___x_125_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11);
v___f_126_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_126_, 0, v___x_125_);
return v___f_126_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14(void){
_start:
{
lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_127_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13);
v___f_128_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___f_128_);
lean_ctor_set(v___x_129_, 1, v___f_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15(void){
_start:
{
lean_object* v___x_130_; lean_object* v___f_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_131_, 0, v___x_130_);
return v___f_131_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16(void){
_start:
{
lean_object* v___x_132_; lean_object* v___f_133_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_133_, 0, v___x_132_);
return v___f_133_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17(void){
_start:
{
lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_136_; 
v___f_134_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16);
v___f_135_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___f_135_);
lean_ctor_set(v___x_136_, 1, v___f_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18(void){
_start:
{
lean_object* v___x_137_; lean_object* v___f_138_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17);
v___f_138_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_138_, 0, v___x_137_);
return v___f_138_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19(void){
_start:
{
lean_object* v___x_139_; lean_object* v___f_140_; 
v___x_139_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17);
v___f_140_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_140_, 0, v___x_139_);
return v___f_140_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20(void){
_start:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; 
v___f_141_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19);
v___f_142_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___f_142_);
lean_ctor_set(v___x_143_, 1, v___f_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21(void){
_start:
{
lean_object* v___x_144_; lean_object* v___f_145_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_145_, 0, v___x_144_);
return v___f_145_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22(void){
_start:
{
lean_object* v___x_146_; lean_object* v___f_147_; 
v___x_146_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_147_, 0, v___x_146_);
return v___f_147_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23(void){
_start:
{
lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_148_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22);
v___f_149_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___f_149_);
lean_ctor_set(v___x_150_, 1, v___f_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24(void){
_start:
{
lean_object* v___x_151_; lean_object* v___f_152_; 
v___x_151_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23);
v___f_152_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_152_, 0, v___x_151_);
return v___f_152_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25(void){
_start:
{
lean_object* v___x_153_; lean_object* v___f_154_; 
v___x_153_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23);
v___f_154_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_154_, 0, v___x_153_);
return v___f_154_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26(void){
_start:
{
lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_155_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25);
v___f_156_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___f_156_);
lean_ctor_set(v___x_157_, 1, v___f_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_163_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30));
v___x_164_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___x_165_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_164_, v___x_163_, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32(void){
_start:
{
lean_object* v___x_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31);
v___f_167_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_168_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_169_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_168_, v___f_167_, v___x_166_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32);
v___x_171_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30));
v___x_172_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___x_173_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_172_, v___x_171_, v___x_170_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34(void){
_start:
{
lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33);
v___f_175_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_176_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_177_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_176_, v___f_175_, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30));
v___x_180_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29));
v___x_181_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_180_, v___x_179_, v___x_178_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36(void){
_start:
{
lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35);
v___f_183_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_184_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_185_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_184_, v___f_183_, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37(void){
_start:
{
lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36);
v___f_187_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_188_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27));
v___x_189_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_188_, v___f_187_, v___x_186_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___f_192_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30));
v___x_191_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_192_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_192_, 0, v___x_191_);
lean_closure_set(v___f_192_, 1, v___x_190_);
return v___f_192_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39(void){
_start:
{
lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; 
v___f_193_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_194_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38);
v___f_195_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_195_, 0, v___f_194_);
lean_closure_set(v___f_195_, 1, v___f_193_);
return v___f_195_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40(void){
_start:
{
lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___f_198_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30));
v___f_197_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_198_, 0, v___f_197_);
lean_closure_set(v___f_198_, 1, v___x_196_);
return v___f_198_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41(void){
_start:
{
lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; 
v___f_199_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_200_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40);
v___f_201_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_201_, 0, v___f_200_);
lean_closure_set(v___f_201_, 1, v___f_199_);
return v___f_201_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42(void){
_start:
{
lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; 
v___f_202_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28));
v___f_203_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41);
v___f_204_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_204_, 0, v___f_203_);
lean_closure_set(v___f_204_, 1, v___f_202_);
return v___f_204_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object* v_00_u03b1_208_){
_start:
{
lean_object* v___x_209_; lean_object* v_toApplicative_210_; lean_object* v_toFunctor_211_; lean_object* v_toSeq_212_; lean_object* v_toSeqLeft_213_; lean_object* v_toSeqRight_214_; lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_toApplicative_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_266_; 
v___x_209_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1);
v_toApplicative_210_ = lean_ctor_get(v___x_209_, 0);
v_toFunctor_211_ = lean_ctor_get(v_toApplicative_210_, 0);
v_toSeq_212_ = lean_ctor_get(v_toApplicative_210_, 2);
v_toSeqLeft_213_ = lean_ctor_get(v_toApplicative_210_, 3);
v_toSeqRight_214_ = lean_ctor_get(v_toApplicative_210_, 4);
v___f_215_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2));
v___f_216_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3));
lean_inc_ref_n(v_toFunctor_211_, 2);
v___f_217_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_217_, 0, v_toFunctor_211_);
v___f_218_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_218_, 0, v_toFunctor_211_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___f_217_);
lean_ctor_set(v___x_219_, 1, v___f_218_);
lean_inc(v_toSeqRight_214_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_220_, 0, v_toSeqRight_214_);
lean_inc(v_toSeqLeft_213_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_221_, 0, v_toSeqLeft_213_);
lean_inc(v_toSeq_212_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_222_, 0, v_toSeq_212_);
v___x_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_223_, 0, v___x_219_);
lean_ctor_set(v___x_223_, 1, v___f_215_);
lean_ctor_set(v___x_223_, 2, v___f_222_);
lean_ctor_set(v___x_223_, 3, v___f_221_);
lean_ctor_set(v___x_223_, 4, v___f_220_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___f_216_);
v___x_225_ = l_StateRefT_x27_instMonad___redArg(v___x_224_);
v_toApplicative_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___x_225_, 1);
lean_dec(v_unused_267_);
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_266_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_toApplicative_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_266_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_toFunctor_230_; lean_object* v_toSeq_231_; lean_object* v_toSeqLeft_232_; lean_object* v_toSeqRight_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_264_; 
v_toFunctor_230_ = lean_ctor_get(v_toApplicative_226_, 0);
v_toSeq_231_ = lean_ctor_get(v_toApplicative_226_, 2);
v_toSeqLeft_232_ = lean_ctor_get(v_toApplicative_226_, 3);
v_toSeqRight_233_ = lean_ctor_get(v_toApplicative_226_, 4);
v_isSharedCheck_264_ = !lean_is_exclusive(v_toApplicative_226_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_toApplicative_226_, 1);
lean_dec(v_unused_265_);
v___x_235_ = v_toApplicative_226_;
v_isShared_236_ = v_isSharedCheck_264_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_toSeqRight_233_);
lean_inc(v_toSeqLeft_232_);
lean_inc(v_toSeq_231_);
lean_inc(v_toFunctor_230_);
lean_dec(v_toApplicative_226_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_264_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_246_; 
v___f_237_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4));
v___f_238_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5));
lean_inc_ref(v_toFunctor_230_);
v___f_239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_239_, 0, v_toFunctor_230_);
v___f_240_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_240_, 0, v_toFunctor_230_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___f_239_);
lean_ctor_set(v___x_241_, 1, v___f_240_);
v___f_242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_242_, 0, v_toSeqRight_233_);
v___f_243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_243_, 0, v_toSeqLeft_232_);
v___f_244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_244_, 0, v_toSeq_231_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 4, v___f_242_);
lean_ctor_set(v___x_235_, 3, v___f_243_);
lean_ctor_set(v___x_235_, 2, v___f_244_);
lean_ctor_set(v___x_235_, 1, v___f_237_);
lean_ctor_set(v___x_235_, 0, v___x_241_);
v___x_246_ = v___x_235_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___f_237_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v___f_244_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v___f_243_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v___f_242_);
v___x_246_ = v_reuseFailAlloc_263_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_248_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___f_238_);
lean_ctor_set(v___x_228_, 0, v___x_246_);
v___x_248_ = v___x_228_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___f_238_);
v___x_248_ = v_reuseFailAlloc_262_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_toMonadRef_256_; lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_249_ = l_StateRefT_x27_instMonad___redArg(v___x_248_);
v___x_250_ = l_ReaderT_instMonad___redArg(v___x_249_);
v___x_251_ = l_StateRefT_x27_instMonad___redArg(v___x_250_);
v___x_252_ = l_ReaderT_instMonad___redArg(v___x_251_);
v___x_253_ = l_ReaderT_instMonad___redArg(v___x_252_);
v___x_254_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26);
v___x_255_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37);
v_toMonadRef_256_ = lean_ctor_get(v___x_255_, 0);
v___f_257_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42);
lean_inc_ref(v___x_253_);
v___x_258_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_257_, v___x_253_);
lean_inc_ref(v_toMonadRef_256_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v___x_254_);
lean_ctor_set(v___x_259_, 1, v_toMonadRef_256_);
lean_ctor_set(v___x_259_, 2, v___x_258_);
v___x_260_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44);
v___x_261_ = l_Lean_throwError___redArg(v___x_253_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_env_275_; lean_object* v___x_276_; lean_object* v_mctx_277_; lean_object* v_lctx_278_; lean_object* v_options_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_274_ = lean_st_ref_get(v___y_272_);
v_env_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc_ref(v_env_275_);
lean_dec(v___x_274_);
v___x_276_ = lean_st_ref_get(v___y_270_);
v_mctx_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref(v_mctx_277_);
lean_dec(v___x_276_);
v_lctx_278_ = lean_ctor_get(v___y_269_, 2);
v_options_279_ = lean_ctor_get(v___y_271_, 2);
lean_inc_ref(v_options_279_);
lean_inc_ref(v_lctx_278_);
v___x_280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_280_, 0, v_env_275_);
lean_ctor_set(v___x_280_, 1, v_mctx_277_);
lean_ctor_set(v___x_280_, 2, v_lctx_278_);
lean_ctor_set(v___x_280_, 3, v_options_279_);
v___x_281_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_msgData_268_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0___boxed(lean_object* v_msgData_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msgData_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_ref_296_; lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_306_; 
v_ref_296_ = lean_ctor_get(v___y_293_, 5);
v___x_297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_306_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
lean_inc(v_ref_296_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_ref_296_);
lean_ctor_set(v___x_302_, 1, v_a_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 1);
lean_ctor_set(v___x_300_, 0, v___x_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg___boxed(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object* v_x_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44);
v___x_326_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v___x_325_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v_x_327_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(lean_object* v_00_u03b1_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_344_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___boxed(lean_object* v_00_u03b1_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(v_00_u03b1_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object* v_m_370_){
_start:
{
lean_inc_ref(v_m_370_);
return v_m_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_371_);
lean_dec_ref(v_m_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object* v_m_373_){
_start:
{
lean_inc(v_m_373_);
return v_m_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_374_);
lean_dec(v_m_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
lean_inc(v_a_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v_a_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_379_);
lean_dec(v_a_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; 
lean_inc(v_a_382_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_a_382_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object* v_x_407_, lean_object* v_methods_408_, lean_object* v_config_409_, lean_object* v_s_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_lctx_418_; lean_object* v_decls_419_; lean_object* v_size_420_; lean_object* v_persistentCache_421_; lean_object* v_funext_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_452_; 
v_lctx_418_ = lean_ctor_get(v_a_413_, 2);
v_decls_419_ = lean_ctor_get(v_lctx_418_, 1);
v_size_420_ = lean_ctor_get(v_decls_419_, 2);
v_persistentCache_421_ = lean_ctor_get(v_s_410_, 1);
v_funext_422_ = lean_ctor_get(v_s_410_, 3);
v_isSharedCheck_452_ = !lean_is_exclusive(v_s_410_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v_s_410_, 2);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_s_410_, 0);
lean_dec(v_unused_454_);
v___x_424_ = v_s_410_;
v_isShared_425_ = v_isSharedCheck_452_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_funext_422_);
lean_inc(v_persistentCache_421_);
lean_dec(v_s_410_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_452_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_426_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_420_);
v___x_427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_427_, 0, v_config_409_);
lean_ctor_set(v___x_427_, 1, v_size_420_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
v___x_428_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 2, v___x_428_);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_persistentCache_421_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_funext_422_);
v___x_430_ = v_reuseFailAlloc_451_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_st_mk_ref(v___x_430_);
lean_inc(v_a_416_);
lean_inc_ref(v_a_415_);
lean_inc(v_a_414_);
lean_inc_ref(v_a_413_);
lean_inc(v_a_412_);
lean_inc_ref(v_a_411_);
lean_inc(v___x_431_);
v___x_432_ = lean_apply_10(v_x_407_, v_methods_408_, v___x_427_, v___x_431_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, lean_box(0));
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_442_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_442_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = lean_st_ref_get(v___x_431_);
lean_dec(v___x_431_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_a_433_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v___x_431_);
v_a_443_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_432_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_432_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object* v_x_455_, lean_object* v_methods_456_, lean_object* v_config_457_, lean_object* v_s_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_455_, v_methods_456_, v_config_457_, v_s_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object* v_00_u03b1_467_, lean_object* v_x_468_, lean_object* v_methods_469_, lean_object* v_config_470_, lean_object* v_s_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_468_, v_methods_469_, v_config_470_, v_s_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object* v_00_u03b1_480_, lean_object* v_x_481_, lean_object* v_methods_482_, lean_object* v_config_483_, lean_object* v_s_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_Sym_Simp_SimpM_run(v_00_u03b1_480_, v_x_481_, v_methods_482_, v_config_483_, v_s_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_492_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_493_);
lean_ctor_set(v___x_495_, 3, v___x_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object* v_x_496_, lean_object* v_methods_497_, lean_object* v_config_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_lctx_506_; lean_object* v_decls_507_; lean_object* v_size_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_lctx_506_ = lean_ctor_get(v_a_501_, 2);
v_decls_507_ = lean_ctor_get(v_lctx_506_, 1);
v_size_508_ = lean_ctor_get(v_decls_507_, 2);
v___x_509_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_508_);
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v_config_498_);
lean_ctor_set(v___x_510_, 1, v_size_508_);
lean_ctor_set(v___x_510_, 2, v___x_509_);
v___x_511_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0);
v___x_512_ = lean_st_mk_ref(v___x_511_);
lean_inc(v_a_504_);
lean_inc_ref(v_a_503_);
lean_inc(v_a_502_);
lean_inc_ref(v_a_501_);
lean_inc(v_a_500_);
lean_inc_ref(v_a_499_);
lean_inc(v___x_512_);
v___x_513_ = lean_apply_10(v_x_496_, v_methods_497_, v___x_510_, v___x_512_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, lean_box(0));
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_st_ref_get(v___x_512_);
lean_dec(v___x_512_);
lean_dec(v___x_518_);
if (v_isShared_517_ == 0)
{
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_514_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_dec(v___x_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object* v_x_523_, lean_object* v_methods_524_, lean_object* v_config_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_523_, v_methods_524_, v_config_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object* v_00_u03b1_534_, lean_object* v_x_535_, lean_object* v_methods_536_, lean_object* v_config_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_535_, v_methods_536_, v_config_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object* v_00_u03b1_546_, lean_object* v_x_547_, lean_object* v_methods_548_, lean_object* v_config_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(v_00_u03b1_546_, v_x_547_, v_methods_548_, v_config_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object* v_a_00___x40___internal___hyg_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_00___x40___internal___hyg_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = lean_sym_simp(v_a_00___x40___internal___hyg_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object* v_a_581_){
_start:
{
lean_object* v_config_583_; lean_object* v___x_584_; 
v_config_583_ = lean_ctor_get(v_a_581_, 0);
lean_inc_ref(v_config_583_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_config_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_585_);
lean_dec_ref(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_589_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object* v_e_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_pre_621_; lean_object* v___x_622_; 
v_pre_621_ = lean_ctor_get(v_a_611_, 0);
lean_inc_ref(v_pre_621_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
lean_inc_ref(v_a_616_);
lean_inc(v_a_615_);
lean_inc_ref(v_a_614_);
lean_inc(v_a_613_);
lean_inc_ref(v_a_612_);
lean_inc(v_a_611_);
v___x_622_ = lean_apply_11(v_pre_621_, v_e_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, lean_box(0));
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object* v_e_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_Sym_Simp_pre(v_e_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_post_646_; lean_object* v___x_647_; 
v_post_646_ = lean_ctor_get(v_a_636_, 1);
lean_inc_ref(v_post_646_);
lean_inc(v_a_644_);
lean_inc_ref(v_a_643_);
lean_inc(v_a_642_);
lean_inc_ref(v_a_641_);
lean_inc(v_a_640_);
lean_inc_ref(v_a_639_);
lean_inc(v_a_638_);
lean_inc_ref(v_a_637_);
lean_inc(v_a_636_);
v___x_647_ = lean_apply_11(v_post_646_, v_e_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_Sym_Simp_post(v_e_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object* v_a_660_, lean_object* v_persistentCache_661_, lean_object* v_transientCache_662_, lean_object* v_funext_663_, lean_object* v_a_x3f_664_){
_start:
{
lean_object* v___x_666_; lean_object* v_numSteps_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_677_; 
v___x_666_ = lean_st_ref_take(v_a_660_);
v_numSteps_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_678_ = lean_ctor_get(v___x_666_, 3);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v___x_666_, 2);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v___x_666_, 1);
lean_dec(v_unused_680_);
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_numSteps_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 3, v_funext_663_);
lean_ctor_set(v___x_669_, 2, v_transientCache_662_);
lean_ctor_set(v___x_669_, 1, v_persistentCache_661_);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_numSteps_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_persistentCache_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_transientCache_662_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_funext_663_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_st_ref_set(v_a_660_, v___x_672_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object* v_a_681_, lean_object* v_persistentCache_682_, lean_object* v_transientCache_683_, lean_object* v_funext_684_, lean_object* v_a_x3f_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_681_, v_persistentCache_682_, v_transientCache_683_, v_funext_684_, v_a_x3f_685_);
lean_dec(v_a_x3f_685_);
lean_dec(v_a_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object* v_k_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_persistentCache_702_; lean_object* v_transientCache_703_; lean_object* v_funext_704_; lean_object* v_r_705_; 
v___x_699_ = lean_st_ref_get(v_a_691_);
v___x_700_ = lean_st_ref_get(v_a_691_);
v___x_701_ = lean_st_ref_get(v_a_691_);
v_persistentCache_702_ = lean_ctor_get(v___x_699_, 1);
lean_inc_ref(v_persistentCache_702_);
lean_dec(v___x_699_);
v_transientCache_703_ = lean_ctor_get(v___x_700_, 2);
lean_inc_ref(v_transientCache_703_);
lean_dec(v___x_700_);
v_funext_704_ = lean_ctor_get(v___x_701_, 3);
lean_inc_ref(v_funext_704_);
lean_dec(v___x_701_);
lean_inc(v_a_697_);
lean_inc_ref(v_a_696_);
lean_inc(v_a_695_);
lean_inc_ref(v_a_694_);
lean_inc(v_a_693_);
lean_inc_ref(v_a_692_);
lean_inc(v_a_691_);
lean_inc_ref(v_a_690_);
lean_inc(v_a_689_);
v_r_705_ = lean_apply_10(v_k_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, lean_box(0));
if (lean_obj_tag(v_r_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_722_; 
v_a_706_ = lean_ctor_get(v_r_705_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_r_705_);
if (v_isSharedCheck_722_ == 0)
{
v___x_708_ = v_r_705_;
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v_r_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
lean_inc(v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_721_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v___x_712_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_691_, v_persistentCache_702_, v_transientCache_703_, v_funext_704_, v___x_711_);
lean_dec_ref(v___x_711_);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_720_);
v___x_714_ = v___x_712_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_712_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_a_706_);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_706_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_723_ = lean_ctor_get(v_r_705_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v_r_705_);
v___x_724_ = lean_box(0);
v___x_725_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_691_, v_persistentCache_702_, v_transientCache_703_, v_funext_704_, v___x_724_);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_733_);
v___x_727_ = v___x_725_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 1);
lean_ctor_set(v___x_727_, 0, v_a_723_);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_723_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object* v_k_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object* v_00_u03b1_746_, lean_object* v_k_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_persistentCache_761_; lean_object* v_transientCache_762_; lean_object* v_funext_763_; lean_object* v_r_764_; 
v___x_758_ = lean_st_ref_get(v_a_750_);
v___x_759_ = lean_st_ref_get(v_a_750_);
v___x_760_ = lean_st_ref_get(v_a_750_);
v_persistentCache_761_ = lean_ctor_get(v___x_758_, 1);
lean_inc_ref(v_persistentCache_761_);
lean_dec(v___x_758_);
v_transientCache_762_ = lean_ctor_get(v___x_759_, 2);
lean_inc_ref(v_transientCache_762_);
lean_dec(v___x_759_);
v_funext_763_ = lean_ctor_get(v___x_760_, 3);
lean_inc_ref(v_funext_763_);
lean_dec(v___x_760_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
lean_inc(v_a_754_);
lean_inc_ref(v_a_753_);
lean_inc(v_a_752_);
lean_inc_ref(v_a_751_);
lean_inc(v_a_750_);
lean_inc_ref(v_a_749_);
lean_inc(v_a_748_);
v_r_764_ = lean_apply_10(v_k_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, lean_box(0));
if (lean_obj_tag(v_r_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_781_; 
v_a_765_ = lean_ctor_get(v_r_764_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_r_764_);
if (v_isSharedCheck_781_ == 0)
{
v___x_767_ = v_r_764_;
v_isShared_768_ = v_isSharedCheck_781_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v_r_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_781_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
lean_inc(v_a_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 1);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_780_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v___x_771_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_750_, v_persistentCache_761_, v_transientCache_762_, v_funext_763_, v___x_770_);
lean_dec_ref(v___x_770_);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___x_771_, 0);
lean_dec(v_unused_779_);
v___x_773_ = v___x_771_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_dec(v___x_771_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_765_);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_765_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_782_ = lean_ctor_get(v_r_764_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v_r_764_);
v___x_783_ = lean_box(0);
v___x_784_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_750_, v_persistentCache_761_, v_transientCache_762_, v_funext_763_, v___x_783_);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_792_);
v___x_786_ = v___x_784_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_dec(v___x_784_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 1);
lean_ctor_set(v___x_786_, 0, v_a_782_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_782_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object* v_00_u03b1_793_, lean_object* v_k_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(v_00_u03b1_793_, v_k_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(lean_object* v_a_806_, lean_object* v_transientCache_807_, lean_object* v_funext_808_, lean_object* v_a_x3f_809_){
_start:
{
lean_object* v___x_811_; lean_object* v_numSteps_812_; lean_object* v_persistentCache_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v___x_811_ = lean_st_ref_take(v_a_806_);
v_numSteps_812_ = lean_ctor_get(v___x_811_, 0);
v_persistentCache_813_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_824_ = lean_ctor_get(v___x_811_, 3);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v___x_811_, 2);
lean_dec(v_unused_825_);
v___x_815_ = v___x_811_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_persistentCache_813_);
lean_inc(v_numSteps_812_);
lean_dec(v___x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 3, v_funext_808_);
lean_ctor_set(v___x_815_, 2, v_transientCache_807_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_numSteps_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_persistentCache_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_transientCache_807_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_funext_808_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_st_ref_set(v_a_806_, v___x_818_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(lean_object* v_a_826_, lean_object* v_transientCache_827_, lean_object* v_funext_828_, lean_object* v_a_x3f_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_826_, v_transientCache_827_, v_funext_828_, v_a_x3f_829_);
lean_dec(v_a_x3f_829_);
lean_dec(v_a_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(lean_object* v_k_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_transientCache_845_; lean_object* v_funext_846_; lean_object* v_r_847_; 
v___x_843_ = lean_st_ref_get(v_a_835_);
v___x_844_ = lean_st_ref_get(v_a_835_);
v_transientCache_845_ = lean_ctor_get(v___x_843_, 2);
lean_inc_ref(v_transientCache_845_);
lean_dec(v___x_843_);
v_funext_846_ = lean_ctor_get(v___x_844_, 3);
lean_inc_ref(v_funext_846_);
lean_dec(v___x_844_);
lean_inc(v_a_841_);
lean_inc_ref(v_a_840_);
lean_inc(v_a_839_);
lean_inc_ref(v_a_838_);
lean_inc(v_a_837_);
lean_inc_ref(v_a_836_);
lean_inc(v_a_835_);
lean_inc_ref(v_a_834_);
lean_inc(v_a_833_);
v_r_847_ = lean_apply_10(v_k_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, lean_box(0));
if (lean_obj_tag(v_r_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_864_; 
v_a_848_ = lean_ctor_get(v_r_847_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_r_847_);
if (v_isSharedCheck_864_ == 0)
{
v___x_850_ = v_r_847_;
v_isShared_851_ = v_isSharedCheck_864_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v_r_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_864_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
lean_inc(v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 1);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_863_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v___x_854_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_835_, v_transientCache_845_, v_funext_846_, v___x_853_);
lean_dec_ref(v___x_853_);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v___x_854_, 0);
lean_dec(v_unused_862_);
v___x_856_ = v___x_854_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_dec(v___x_854_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v_a_848_);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_848_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_865_ = lean_ctor_get(v_r_847_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v_r_847_);
v___x_866_ = lean_box(0);
v___x_867_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_835_, v_transientCache_845_, v_funext_846_, v___x_866_);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_875_);
v___x_869_ = v___x_867_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_dec(v___x_867_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 1);
lean_ctor_set(v___x_869_, 0, v_a_865_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_865_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(lean_object* v_k_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(v_k_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_object* v_00_u03b1_888_, lean_object* v_k_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_transientCache_902_; lean_object* v_funext_903_; lean_object* v_r_904_; 
v___x_900_ = lean_st_ref_get(v_a_892_);
v___x_901_ = lean_st_ref_get(v_a_892_);
v_transientCache_902_ = lean_ctor_get(v___x_900_, 2);
lean_inc_ref(v_transientCache_902_);
lean_dec(v___x_900_);
v_funext_903_ = lean_ctor_get(v___x_901_, 3);
lean_inc_ref(v_funext_903_);
lean_dec(v___x_901_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_a_894_);
lean_inc_ref(v_a_893_);
lean_inc(v_a_892_);
lean_inc_ref(v_a_891_);
lean_inc(v_a_890_);
v_r_904_ = lean_apply_10(v_k_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, lean_box(0));
if (lean_obj_tag(v_r_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_921_; 
v_a_905_ = lean_ctor_get(v_r_904_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_r_904_);
if (v_isSharedCheck_921_ == 0)
{
v___x_907_ = v_r_904_;
v_isShared_908_ = v_isSharedCheck_921_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v_r_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_921_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
lean_inc(v_a_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_920_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v___x_911_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_892_, v_transientCache_902_, v_funext_903_, v___x_910_);
lean_dec_ref(v___x_910_);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_919_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v_a_905_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_905_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_922_ = lean_ctor_get(v_r_904_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v_r_904_);
v___x_923_ = lean_box(0);
v___x_924_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_892_, v_transientCache_902_, v_funext_903_, v___x_923_);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v___x_924_, 0);
lean_dec(v_unused_932_);
v___x_926_ = v___x_924_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_924_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 1);
lean_ctor_set(v___x_926_, 0, v_a_922_);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_922_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(lean_object* v_00_u03b1_933_, lean_object* v_k_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(v_00_u03b1_933_, v_k_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp(lean_object* v_e_946_, lean_object* v_methods_947_, lean_object* v_config_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_956_, 0, v_e_946_);
v___x_957_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_956_, v_methods_947_, v_config_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object* v_e_958_, lean_object* v_methods_959_, lean_object* v_config_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_Sym_simp(v_e_958_, v_methods_959_, v_config_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
return v_res_968_;
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
