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
lean_object* v___x_209_; lean_object* v_toApplicative_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_280_; 
v___x_209_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1);
v_toApplicative_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_209_, 1);
lean_dec(v_unused_281_);
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_280_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_toApplicative_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_280_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_toFunctor_214_; lean_object* v_toSeq_215_; lean_object* v_toSeqLeft_216_; lean_object* v_toSeqRight_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_278_; 
v_toFunctor_214_ = lean_ctor_get(v_toApplicative_210_, 0);
v_toSeq_215_ = lean_ctor_get(v_toApplicative_210_, 2);
v_toSeqLeft_216_ = lean_ctor_get(v_toApplicative_210_, 3);
v_toSeqRight_217_ = lean_ctor_get(v_toApplicative_210_, 4);
v_isSharedCheck_278_ = !lean_is_exclusive(v_toApplicative_210_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_dec(v_unused_279_);
v___x_219_ = v_toApplicative_210_;
v_isShared_220_ = v_isSharedCheck_278_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_toSeqRight_217_);
lean_inc(v_toSeqLeft_216_);
lean_inc(v_toSeq_215_);
lean_inc(v_toFunctor_214_);
lean_dec(v_toApplicative_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_278_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_230_; 
v___f_221_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2));
v___f_222_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3));
lean_inc_ref(v_toFunctor_214_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_223_, 0, v_toFunctor_214_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_224_, 0, v_toFunctor_214_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___f_223_);
lean_ctor_set(v___x_225_, 1, v___f_224_);
v___f_226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_226_, 0, v_toSeqRight_217_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_227_, 0, v_toSeqLeft_216_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_228_, 0, v_toSeq_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 4, v___f_226_);
lean_ctor_set(v___x_219_, 3, v___f_227_);
lean_ctor_set(v___x_219_, 2, v___f_228_);
lean_ctor_set(v___x_219_, 1, v___f_221_);
lean_ctor_set(v___x_219_, 0, v___x_225_);
v___x_230_ = v___x_219_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v___f_228_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v___f_227_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___f_226_);
v___x_230_ = v_reuseFailAlloc_277_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___f_222_);
lean_ctor_set(v___x_212_, 0, v___x_230_);
v___x_232_ = v___x_212_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___f_222_);
v___x_232_ = v_reuseFailAlloc_276_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v_toApplicative_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_274_; 
v___x_233_ = l_StateRefT_x27_instMonad___redArg(v___x_232_);
v_toApplicative_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_233_, 1);
lean_dec(v_unused_275_);
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_274_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_toApplicative_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_274_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_toFunctor_238_; lean_object* v_toSeq_239_; lean_object* v_toSeqLeft_240_; lean_object* v_toSeqRight_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_272_; 
v_toFunctor_238_ = lean_ctor_get(v_toApplicative_234_, 0);
v_toSeq_239_ = lean_ctor_get(v_toApplicative_234_, 2);
v_toSeqLeft_240_ = lean_ctor_get(v_toApplicative_234_, 3);
v_toSeqRight_241_ = lean_ctor_get(v_toApplicative_234_, 4);
v_isSharedCheck_272_ = !lean_is_exclusive(v_toApplicative_234_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_toApplicative_234_, 1);
lean_dec(v_unused_273_);
v___x_243_ = v_toApplicative_234_;
v_isShared_244_ = v_isSharedCheck_272_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_toSeqRight_241_);
lean_inc(v_toSeqLeft_240_);
lean_inc(v_toSeq_239_);
lean_inc(v_toFunctor_238_);
lean_dec(v_toApplicative_234_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_272_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___x_254_; 
v___f_245_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4));
v___f_246_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5));
lean_inc_ref(v_toFunctor_238_);
v___f_247_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_247_, 0, v_toFunctor_238_);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_248_, 0, v_toFunctor_238_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___f_247_);
lean_ctor_set(v___x_249_, 1, v___f_248_);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_250_, 0, v_toSeqRight_241_);
v___f_251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_251_, 0, v_toSeqLeft_240_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_252_, 0, v_toSeq_239_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 4, v___f_250_);
lean_ctor_set(v___x_243_, 3, v___f_251_);
lean_ctor_set(v___x_243_, 2, v___f_252_);
lean_ctor_set(v___x_243_, 1, v___f_245_);
lean_ctor_set(v___x_243_, 0, v___x_249_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___f_245_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v___f_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v___f_251_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v___f_250_);
v___x_254_ = v_reuseFailAlloc_271_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v___f_246_);
lean_ctor_set(v___x_236_, 0, v___x_254_);
v___x_256_ = v___x_236_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___f_246_);
v___x_256_ = v_reuseFailAlloc_270_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_toMonadRef_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_257_ = l_StateRefT_x27_instMonad___redArg(v___x_256_);
v___x_258_ = l_ReaderT_instMonad___redArg(v___x_257_);
v___x_259_ = l_StateRefT_x27_instMonad___redArg(v___x_258_);
v___x_260_ = l_ReaderT_instMonad___redArg(v___x_259_);
v___x_261_ = l_ReaderT_instMonad___redArg(v___x_260_);
v___x_262_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37);
v_toMonadRef_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_ref(v_toMonadRef_264_);
v___f_265_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42);
lean_inc_ref(v___x_261_);
v___x_266_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_265_, v___x_261_);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_262_);
lean_ctor_set(v___x_267_, 1, v_toMonadRef_264_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
v___x_268_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44);
v___x_269_ = l_Lean_throwError___redArg(v___x_261_, v___x_267_, v___x_268_);
return v___x_269_;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_lctx_292_ = lean_ctor_get(v___y_283_, 2);
v_options_293_ = lean_ctor_get(v___y_285_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_289_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_282_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_ref_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_ref_310_ = lean_ctor_get(v___y_307_, 5);
v___x_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0_spec__0(v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_inc(v_ref_310_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_ref_310_);
lean_ctor_set(v___x_316_, 1, v_a_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 1);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg___boxed(lean_object* v_msg_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44);
v___x_340_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v___x_339_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v_x_341_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1(void){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; 
v___f_354_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0));
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___f_354_);
lean_ctor_set(v___x_355_, 1, v___f_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(lean_object* v_00_u03b1_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___redArg(v_msg_358_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_instInhabitedMethods_default_spec__0(v_00_u03b1_370_, v_msg_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedMethods(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default;
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object* v_m_384_){
_start:
{
lean_inc_ref(v_m_384_);
return v_m_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_385_);
lean_dec_ref(v_m_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object* v_m_387_){
_start:
{
lean_inc(v_m_387_);
return v_m_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_388_);
lean_dec(v_m_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; 
lean_inc(v_a_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_a_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_393_);
lean_dec(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; 
lean_inc(v_a_396_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_a_396_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
return v_res_417_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object* v_x_421_, lean_object* v_methods_422_, lean_object* v_config_423_, lean_object* v_s_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_lctx_432_; lean_object* v_decls_433_; lean_object* v_size_434_; lean_object* v_persistentCache_435_; lean_object* v_funext_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_466_; 
v_lctx_432_ = lean_ctor_get(v_a_427_, 2);
v_decls_433_ = lean_ctor_get(v_lctx_432_, 1);
v_size_434_ = lean_ctor_get(v_decls_433_, 2);
v_persistentCache_435_ = lean_ctor_get(v_s_424_, 1);
v_funext_436_ = lean_ctor_get(v_s_424_, 3);
v_isSharedCheck_466_ = !lean_is_exclusive(v_s_424_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_s_424_, 2);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_s_424_, 0);
lean_dec(v_unused_468_);
v___x_438_ = v_s_424_;
v_isShared_439_ = v_isSharedCheck_466_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_funext_436_);
lean_inc(v_persistentCache_435_);
lean_dec(v_s_424_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_466_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_440_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_434_);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_config_423_);
lean_ctor_set(v___x_441_, 1, v_size_434_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
v___x_442_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 2, v___x_442_);
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_persistentCache_435_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_funext_436_);
v___x_444_ = v_reuseFailAlloc_465_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_st_mk_ref(v___x_444_);
lean_inc(v_a_430_);
lean_inc_ref(v_a_429_);
lean_inc(v_a_428_);
lean_inc_ref(v_a_427_);
lean_inc(v_a_426_);
lean_inc_ref(v_a_425_);
lean_inc(v___x_445_);
v___x_446_ = lean_apply_10(v_x_421_, v_methods_422_, v___x_441_, v___x_445_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, lean_box(0));
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_456_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = lean_st_ref_get(v___x_445_);
lean_dec(v___x_445_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_a_447_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v___x_445_);
v_a_457_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_446_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object* v_x_469_, lean_object* v_methods_470_, lean_object* v_config_471_, lean_object* v_s_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_469_, v_methods_470_, v_config_471_, v_s_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object* v_00_u03b1_481_, lean_object* v_x_482_, lean_object* v_methods_483_, lean_object* v_config_484_, lean_object* v_s_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_482_, v_methods_483_, v_config_484_, v_s_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object* v_00_u03b1_494_, lean_object* v_x_495_, lean_object* v_methods_496_, lean_object* v_config_497_, lean_object* v_s_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Sym_Simp_SimpM_run(v_00_u03b1_494_, v_x_495_, v_methods_496_, v_config_497_, v_s_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_507_);
lean_ctor_set(v___x_509_, 3, v___x_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object* v_x_510_, lean_object* v_methods_511_, lean_object* v_config_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_lctx_520_; lean_object* v_decls_521_; lean_object* v_size_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_lctx_520_ = lean_ctor_get(v_a_515_, 2);
v_decls_521_ = lean_ctor_get(v_lctx_520_, 1);
v_size_522_ = lean_ctor_get(v_decls_521_, 2);
v___x_523_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_522_);
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v_config_512_);
lean_ctor_set(v___x_524_, 1, v_size_522_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0);
v___x_526_ = lean_st_mk_ref(v___x_525_);
lean_inc(v_a_518_);
lean_inc_ref(v_a_517_);
lean_inc(v_a_516_);
lean_inc_ref(v_a_515_);
lean_inc(v_a_514_);
lean_inc_ref(v_a_513_);
lean_inc(v___x_526_);
v___x_527_ = lean_apply_10(v_x_510_, v_methods_511_, v___x_524_, v___x_526_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, lean_box(0));
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_st_ref_get(v___x_526_);
lean_dec(v___x_526_);
lean_dec(v___x_532_);
if (v_isShared_531_ == 0)
{
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_dec(v___x_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object* v_x_537_, lean_object* v_methods_538_, lean_object* v_config_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_537_, v_methods_538_, v_config_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object* v_00_u03b1_548_, lean_object* v_x_549_, lean_object* v_methods_550_, lean_object* v_config_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_549_, v_methods_550_, v_config_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object* v_00_u03b1_560_, lean_object* v_x_561_, lean_object* v_methods_562_, lean_object* v_config_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(v_00_u03b1_560_, v_x_561_, v_methods_562_, v_config_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object* v_a_00___x40___internal___hyg_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_00___x40___internal___hyg_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = lean_sym_simp(v_a_00___x40___internal___hyg_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object* v_a_595_){
_start:
{
lean_object* v_config_597_; lean_object* v___x_598_; 
v_config_597_ = lean_ctor_get(v_a_595_, 0);
lean_inc_ref(v_config_597_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v_config_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_599_);
lean_dec_ref(v_a_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_603_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_pre_635_; lean_object* v___x_636_; 
v_pre_635_ = lean_ctor_get(v_a_625_, 0);
lean_inc_ref(v_pre_635_);
lean_inc(v_a_633_);
lean_inc_ref(v_a_632_);
lean_inc(v_a_631_);
lean_inc_ref(v_a_630_);
lean_inc(v_a_629_);
lean_inc_ref(v_a_628_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
v___x_636_ = lean_apply_11(v_pre_635_, v_e_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, lean_box(0));
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Meta_Sym_Simp_pre(v_e_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_post_660_; lean_object* v___x_661_; 
v_post_660_ = lean_ctor_get(v_a_650_, 1);
lean_inc_ref(v_post_660_);
lean_inc(v_a_658_);
lean_inc_ref(v_a_657_);
lean_inc(v_a_656_);
lean_inc_ref(v_a_655_);
lean_inc(v_a_654_);
lean_inc_ref(v_a_653_);
lean_inc(v_a_652_);
lean_inc_ref(v_a_651_);
v___x_661_ = lean_apply_11(v_post_660_, v_e_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, lean_box(0));
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Meta_Sym_Simp_post(v_e_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object* v_a_674_, lean_object* v_persistentCache_675_, lean_object* v_transientCache_676_, lean_object* v_funext_677_, lean_object* v_a_x3f_678_){
_start:
{
lean_object* v___x_680_; lean_object* v_numSteps_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_691_; 
v___x_680_ = lean_st_ref_take(v_a_674_);
v_numSteps_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; 
v_unused_692_ = lean_ctor_get(v___x_680_, 3);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v___x_680_, 2);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v___x_680_, 1);
lean_dec(v_unused_694_);
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_691_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_numSteps_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_691_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 3, v_funext_677_);
lean_ctor_set(v___x_683_, 2, v_transientCache_676_);
lean_ctor_set(v___x_683_, 1, v_persistentCache_675_);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_numSteps_681_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_persistentCache_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_transientCache_676_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_funext_677_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_st_ref_set(v_a_674_, v___x_686_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object* v_a_695_, lean_object* v_persistentCache_696_, lean_object* v_transientCache_697_, lean_object* v_funext_698_, lean_object* v_a_x3f_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_695_, v_persistentCache_696_, v_transientCache_697_, v_funext_698_, v_a_x3f_699_);
lean_dec(v_a_x3f_699_);
lean_dec(v_a_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object* v_k_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_persistentCache_716_; lean_object* v_transientCache_717_; lean_object* v_funext_718_; lean_object* v_r_719_; 
v___x_713_ = lean_st_ref_get(v_a_705_);
v___x_714_ = lean_st_ref_get(v_a_705_);
v___x_715_ = lean_st_ref_get(v_a_705_);
v_persistentCache_716_ = lean_ctor_get(v___x_713_, 1);
lean_inc_ref(v_persistentCache_716_);
lean_dec(v___x_713_);
v_transientCache_717_ = lean_ctor_get(v___x_714_, 2);
lean_inc_ref(v_transientCache_717_);
lean_dec(v___x_714_);
v_funext_718_ = lean_ctor_get(v___x_715_, 3);
lean_inc_ref(v_funext_718_);
lean_dec(v___x_715_);
lean_inc(v_a_711_);
lean_inc_ref(v_a_710_);
lean_inc(v_a_709_);
lean_inc_ref(v_a_708_);
lean_inc(v_a_707_);
lean_inc_ref(v_a_706_);
lean_inc(v_a_705_);
lean_inc_ref(v_a_704_);
lean_inc(v_a_703_);
v_r_719_ = lean_apply_10(v_k_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, lean_box(0));
if (lean_obj_tag(v_r_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_736_; 
v_a_720_ = lean_ctor_get(v_r_719_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_r_719_);
if (v_isSharedCheck_736_ == 0)
{
v___x_722_ = v_r_719_;
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v_r_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
lean_inc(v_a_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_735_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v___x_726_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_705_, v_persistentCache_716_, v_transientCache_717_, v_funext_718_, v___x_725_);
lean_dec_ref(v___x_725_);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_726_, 0);
lean_dec(v_unused_734_);
v___x_728_ = v___x_726_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_dec(v___x_726_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_a_720_);
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_720_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_737_ = lean_ctor_get(v_r_719_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v_r_719_);
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_705_, v_persistentCache_716_, v_transientCache_717_, v_funext_718_, v___x_738_);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_739_, 0);
lean_dec(v_unused_747_);
v___x_741_ = v___x_739_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_dec(v___x_739_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 1);
lean_ctor_set(v___x_741_, 0, v_a_737_);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_737_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object* v_k_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object* v_00_u03b1_760_, lean_object* v_k_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_persistentCache_775_; lean_object* v_transientCache_776_; lean_object* v_funext_777_; lean_object* v_r_778_; 
v___x_772_ = lean_st_ref_get(v_a_764_);
v___x_773_ = lean_st_ref_get(v_a_764_);
v___x_774_ = lean_st_ref_get(v_a_764_);
v_persistentCache_775_ = lean_ctor_get(v___x_772_, 1);
lean_inc_ref(v_persistentCache_775_);
lean_dec(v___x_772_);
v_transientCache_776_ = lean_ctor_get(v___x_773_, 2);
lean_inc_ref(v_transientCache_776_);
lean_dec(v___x_773_);
v_funext_777_ = lean_ctor_get(v___x_774_, 3);
lean_inc_ref(v_funext_777_);
lean_dec(v___x_774_);
lean_inc(v_a_770_);
lean_inc_ref(v_a_769_);
lean_inc(v_a_768_);
lean_inc_ref(v_a_767_);
lean_inc(v_a_766_);
lean_inc_ref(v_a_765_);
lean_inc(v_a_764_);
lean_inc_ref(v_a_763_);
lean_inc(v_a_762_);
v_r_778_ = lean_apply_10(v_k_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, lean_box(0));
if (lean_obj_tag(v_r_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_795_; 
v_a_779_ = lean_ctor_get(v_r_778_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_r_778_);
if (v_isSharedCheck_795_ == 0)
{
v___x_781_ = v_r_778_;
v_isShared_782_ = v_isSharedCheck_795_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v_r_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_795_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
lean_inc(v_a_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 1);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_794_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v___x_785_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_764_, v_persistentCache_775_, v_transientCache_776_, v_funext_777_, v___x_784_);
lean_dec_ref(v___x_784_);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_785_, 0);
lean_dec(v_unused_793_);
v___x_787_ = v___x_785_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_dec(v___x_785_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_a_779_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_779_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_796_ = lean_ctor_get(v_r_778_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v_r_778_);
v___x_797_ = lean_box(0);
v___x_798_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_764_, v_persistentCache_775_, v_transientCache_776_, v_funext_777_, v___x_797_);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_798_, 0);
lean_dec(v_unused_806_);
v___x_800_ = v___x_798_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_dec(v___x_798_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 0, v_a_796_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_796_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object* v_00_u03b1_807_, lean_object* v_k_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(v_00_u03b1_807_, v_k_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(lean_object* v_a_820_, lean_object* v_transientCache_821_, lean_object* v_funext_822_, lean_object* v_a_x3f_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_numSteps_826_; lean_object* v_persistentCache_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_837_; 
v___x_825_ = lean_st_ref_take(v_a_820_);
v_numSteps_826_ = lean_ctor_get(v___x_825_, 0);
v_persistentCache_827_ = lean_ctor_get(v___x_825_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; 
v_unused_838_ = lean_ctor_get(v___x_825_, 3);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v___x_825_, 2);
lean_dec(v_unused_839_);
v___x_829_ = v___x_825_;
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_persistentCache_827_);
lean_inc(v_numSteps_826_);
lean_dec(v___x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 3, v_funext_822_);
lean_ctor_set(v___x_829_, 2, v_transientCache_821_);
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_numSteps_826_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_persistentCache_827_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_transientCache_821_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_funext_822_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_st_ref_set(v_a_820_, v___x_832_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(lean_object* v_a_840_, lean_object* v_transientCache_841_, lean_object* v_funext_842_, lean_object* v_a_x3f_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_840_, v_transientCache_841_, v_funext_842_, v_a_x3f_843_);
lean_dec(v_a_x3f_843_);
lean_dec(v_a_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(lean_object* v_k_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_transientCache_859_; lean_object* v_funext_860_; lean_object* v_r_861_; 
v___x_857_ = lean_st_ref_get(v_a_849_);
v___x_858_ = lean_st_ref_get(v_a_849_);
v_transientCache_859_ = lean_ctor_get(v___x_857_, 2);
lean_inc_ref(v_transientCache_859_);
lean_dec(v___x_857_);
v_funext_860_ = lean_ctor_get(v___x_858_, 3);
lean_inc_ref(v_funext_860_);
lean_dec(v___x_858_);
lean_inc(v_a_855_);
lean_inc_ref(v_a_854_);
lean_inc(v_a_853_);
lean_inc_ref(v_a_852_);
lean_inc(v_a_851_);
lean_inc_ref(v_a_850_);
lean_inc(v_a_849_);
lean_inc_ref(v_a_848_);
lean_inc(v_a_847_);
v_r_861_ = lean_apply_10(v_k_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, lean_box(0));
if (lean_obj_tag(v_r_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_878_; 
v_a_862_ = lean_ctor_get(v_r_861_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_r_861_);
if (v_isSharedCheck_878_ == 0)
{
v___x_864_ = v_r_861_;
v_isShared_865_ = v_isSharedCheck_878_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v_r_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_878_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
lean_inc(v_a_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 1);
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_877_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v___x_868_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_849_, v_transientCache_859_, v_funext_860_, v___x_867_);
lean_dec_ref(v___x_867_);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v___x_868_, 0);
lean_dec(v_unused_876_);
v___x_870_ = v___x_868_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_dec(v___x_868_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_a_862_);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_862_);
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
}
else
{
lean_object* v_a_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_879_ = lean_ctor_get(v_r_861_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v_r_861_);
v___x_880_ = lean_box(0);
v___x_881_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_849_, v_transientCache_859_, v_funext_860_, v___x_880_);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v___x_881_, 0);
lean_dec(v_unused_889_);
v___x_883_ = v___x_881_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_881_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 1);
lean_ctor_set(v___x_883_, 0, v_a_879_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_879_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(lean_object* v_k_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(v_k_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_object* v_00_u03b1_902_, lean_object* v_k_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_transientCache_916_; lean_object* v_funext_917_; lean_object* v_r_918_; 
v___x_914_ = lean_st_ref_get(v_a_906_);
v___x_915_ = lean_st_ref_get(v_a_906_);
v_transientCache_916_ = lean_ctor_get(v___x_914_, 2);
lean_inc_ref(v_transientCache_916_);
lean_dec(v___x_914_);
v_funext_917_ = lean_ctor_get(v___x_915_, 3);
lean_inc_ref(v_funext_917_);
lean_dec(v___x_915_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc_ref(v_a_907_);
lean_inc(v_a_906_);
lean_inc_ref(v_a_905_);
lean_inc(v_a_904_);
v_r_918_ = lean_apply_10(v_k_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, lean_box(0));
if (lean_obj_tag(v_r_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_935_; 
v_a_919_ = lean_ctor_get(v_r_918_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_r_918_);
if (v_isSharedCheck_935_ == 0)
{
v___x_921_ = v_r_918_;
v_isShared_922_ = v_isSharedCheck_935_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v_r_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_935_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
lean_inc(v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 1);
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_934_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v___x_925_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_906_, v_transientCache_916_, v_funext_917_, v___x_924_);
lean_dec_ref(v___x_924_);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v___x_925_, 0);
lean_dec(v_unused_933_);
v___x_927_ = v___x_925_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_dec(v___x_925_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_a_919_);
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_919_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_936_ = lean_ctor_get(v_r_918_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v_r_918_);
v___x_937_ = lean_box(0);
v___x_938_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_906_, v_transientCache_916_, v_funext_917_, v___x_937_);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_938_, 0);
lean_dec(v_unused_946_);
v___x_940_ = v___x_938_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_dec(v___x_938_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 0, v_a_936_);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_936_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(lean_object* v_00_u03b1_947_, lean_object* v_k_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(v_00_u03b1_947_, v_k_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp(lean_object* v_e_960_, lean_object* v_methods_961_, lean_object* v_config_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_970_, 0, v_e_960_);
v___x_971_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_970_, v_methods_961_, v_config_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object* v_e_972_, lean_object* v_methods_973_, lean_object* v_config_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_Sym_simp(v_e_972_, v_methods_973_, v_config_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_982_;
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
