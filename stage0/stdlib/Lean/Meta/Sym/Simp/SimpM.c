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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___impl___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42;
static const lean_string_object l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<default>"};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__43 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value),((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value;
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
static const lean_closure_object l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___impl(lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_ctorIdx___impl___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Sym_Simp_Result_ctorIdx___impl(v_x_8_);
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
lean_dec_ref_known(v_t_10_, 0);
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
lean_dec_ref_known(v_t_10_, 2);
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
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_instMonadEIO___redArg();
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0);
v___x_104_ = l_StateRefT_x27_instMonad___redArg(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6(void){
_start:
{
lean_object* v___x_109_; lean_object* v___f_110_; 
v___x_109_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_110_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_110_, 0, v___x_109_);
return v___f_110_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_112_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8(void){
_start:
{
lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v___f_113_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7);
v___f_114_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___f_114_);
lean_ctor_set(v___x_115_, 1, v___f_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9(void){
_start:
{
lean_object* v___x_116_; lean_object* v___f_117_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_117_, 0, v___x_116_);
return v___f_117_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10(void){
_start:
{
lean_object* v___x_118_; lean_object* v___f_119_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8);
v___f_119_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_119_, 0, v___x_118_);
return v___f_119_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11(void){
_start:
{
lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_120_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10);
v___f_121_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___f_121_);
lean_ctor_set(v___x_122_, 1, v___f_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12(void){
_start:
{
lean_object* v___x_123_; lean_object* v___f_124_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11);
v___f_124_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_124_, 0, v___x_123_);
return v___f_124_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13(void){
_start:
{
lean_object* v___x_125_; lean_object* v___f_126_; 
v___x_125_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11);
v___f_126_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_126_, 0, v___x_125_);
return v___f_126_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14(void){
_start:
{
lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_127_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13);
v___f_128_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___f_128_);
lean_ctor_set(v___x_129_, 1, v___f_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15(void){
_start:
{
lean_object* v___x_130_; lean_object* v___f_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_131_, 0, v___x_130_);
return v___f_131_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16(void){
_start:
{
lean_object* v___x_132_; lean_object* v___f_133_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_133_, 0, v___x_132_);
return v___f_133_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17(void){
_start:
{
lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_136_; 
v___f_134_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16);
v___f_135_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___f_135_);
lean_ctor_set(v___x_136_, 1, v___f_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18(void){
_start:
{
lean_object* v___x_137_; lean_object* v___f_138_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17);
v___f_138_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_138_, 0, v___x_137_);
return v___f_138_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19(void){
_start:
{
lean_object* v___x_139_; lean_object* v___f_140_; 
v___x_139_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17);
v___f_140_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_140_, 0, v___x_139_);
return v___f_140_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20(void){
_start:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; 
v___f_141_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19);
v___f_142_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___f_142_);
lean_ctor_set(v___x_143_, 1, v___f_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21(void){
_start:
{
lean_object* v___x_144_; lean_object* v___f_145_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_145_, 0, v___x_144_);
return v___f_145_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22(void){
_start:
{
lean_object* v___x_146_; lean_object* v___f_147_; 
v___x_146_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_147_, 0, v___x_146_);
return v___f_147_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23(void){
_start:
{
lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_148_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22);
v___f_149_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___f_149_);
lean_ctor_set(v___x_150_, 1, v___f_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24(void){
_start:
{
lean_object* v___x_151_; lean_object* v___f_152_; 
v___x_151_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23);
v___f_152_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_152_, 0, v___x_151_);
return v___f_152_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25(void){
_start:
{
lean_object* v___x_153_; lean_object* v___f_154_; 
v___x_153_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23);
v___f_154_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_154_, 0, v___x_153_);
return v___f_154_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26(void){
_start:
{
lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_155_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25);
v___f_156_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___f_156_);
lean_ctor_set(v___x_157_, 1, v___f_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_163_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_164_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29));
v___x_165_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_164_, v___x_163_, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32(void){
_start:
{
lean_object* v___x_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31);
v___f_167_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_168_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_169_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_168_, v___f_167_, v___x_166_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32);
v___x_171_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_172_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29));
v___x_173_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_172_, v___x_171_, v___x_170_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34(void){
_start:
{
lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33);
v___f_175_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_176_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_177_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_176_, v___f_175_, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_180_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29));
v___x_181_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_180_, v___x_179_, v___x_178_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36(void){
_start:
{
lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35);
v___f_183_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_184_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_185_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_184_, v___f_183_, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37(void){
_start:
{
lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36);
v___f_187_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_188_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_189_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_188_, v___f_187_, v___x_186_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___f_192_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_191_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_192_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_192_, 0, v___x_191_);
lean_closure_set(v___f_192_, 1, v___x_190_);
return v___f_192_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39(void){
_start:
{
lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; 
v___f_193_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_194_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38);
v___f_195_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_195_, 0, v___f_194_);
lean_closure_set(v___f_195_, 1, v___f_193_);
return v___f_195_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40(void){
_start:
{
lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___f_198_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___f_197_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_198_, 0, v___f_197_);
lean_closure_set(v___f_198_, 1, v___x_196_);
return v___f_198_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41(void){
_start:
{
lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; 
v___f_199_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_200_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40);
v___f_201_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_201_, 0, v___f_200_);
lean_closure_set(v___f_201_, 1, v___f_199_);
return v___f_201_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42(void){
_start:
{
lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; 
v___f_202_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_203_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41);
v___f_204_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_204_, 0, v___f_203_);
lean_closure_set(v___f_204_, 1, v___f_202_);
return v___f_204_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__43));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg(){
_start:
{
lean_object* v___x_209_; lean_object* v_toApplicative_210_; lean_object* v_toFunctor_211_; lean_object* v_toSeq_212_; lean_object* v_toSeqLeft_213_; lean_object* v_toSeqRight_214_; lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_toApplicative_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_266_; 
v___x_209_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1);
v_toApplicative_210_ = lean_ctor_get(v___x_209_, 0);
v_toFunctor_211_ = lean_ctor_get(v_toApplicative_210_, 0);
v_toSeq_212_ = lean_ctor_get(v_toApplicative_210_, 2);
v_toSeqLeft_213_ = lean_ctor_get(v_toApplicative_210_, 3);
v_toSeqRight_214_ = lean_ctor_get(v_toApplicative_210_, 4);
v___f_215_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__2));
v___f_216_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__3));
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
v___f_237_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__4));
v___f_238_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__5));
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
v___x_254_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26);
v___x_255_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37);
v_toMonadRef_256_ = lean_ctor_get(v___x_255_, 0);
v___f_257_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42);
lean_inc_ref(v___x_253_);
v___x_258_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_257_, v___x_253_);
lean_inc_ref(v_toMonadRef_256_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v___x_254_);
lean_ctor_set(v___x_259_, 1, v_toMonadRef_256_);
lean_ctor_set(v___x_259_, 2, v___x_258_);
v___x_260_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44);
v___x_261_ = l_Lean_throwError___redArg(v___x_253_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___boxed(lean_object* v___dummy_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v_res_269_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object* v_00_u03b1_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0));
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v_x_286_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object* v_m_303_){
_start:
{
lean_inc_ref(v_m_303_);
return v_m_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_304_);
lean_dec_ref(v_m_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object* v_m_306_){
_start:
{
lean_inc(v_m_306_);
return v_m_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_307_);
lean_dec(v_m_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
lean_inc(v_a_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_a_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_312_);
lean_dec(v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
lean_inc(v_a_315_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_315_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
return v_res_336_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object* v_x_340_, lean_object* v_methods_341_, lean_object* v_config_342_, lean_object* v_s_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_lctx_351_; lean_object* v_decls_352_; lean_object* v_size_353_; lean_object* v_persistentCache_354_; lean_object* v_funext_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_385_; 
v_lctx_351_ = lean_ctor_get(v_a_346_, 2);
v_decls_352_ = lean_ctor_get(v_lctx_351_, 1);
v_size_353_ = lean_ctor_get(v_decls_352_, 2);
v_persistentCache_354_ = lean_ctor_get(v_s_343_, 1);
v_funext_355_ = lean_ctor_get(v_s_343_, 3);
v_isSharedCheck_385_ = !lean_is_exclusive(v_s_343_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_386_ = lean_ctor_get(v_s_343_, 2);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_s_343_, 0);
lean_dec(v_unused_387_);
v___x_357_ = v_s_343_;
v_isShared_358_ = v_isSharedCheck_385_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_funext_355_);
lean_inc(v_persistentCache_354_);
lean_dec(v_s_343_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_385_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_359_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_353_);
v___x_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_360_, 0, v_config_342_);
lean_ctor_set(v___x_360_, 1, v_size_353_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 2, v___x_361_);
lean_ctor_set(v___x_357_, 0, v___x_359_);
v___x_363_ = v___x_357_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_persistentCache_354_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_funext_355_);
v___x_363_ = v_reuseFailAlloc_384_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_st_mk_ref(v___x_363_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc(v_a_345_);
lean_inc_ref(v_a_344_);
lean_inc(v___x_364_);
v___x_365_ = lean_apply_10(v_x_340_, v_methods_341_, v___x_360_, v___x_364_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, lean_box(0));
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_st_ref_get(v___x_364_);
lean_dec(v___x_364_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_a_366_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v___x_364_);
v_a_376_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_365_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_365_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object* v_x_388_, lean_object* v_methods_389_, lean_object* v_config_390_, lean_object* v_s_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_388_, v_methods_389_, v_config_390_, v_s_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object* v_00_u03b1_400_, lean_object* v_x_401_, lean_object* v_methods_402_, lean_object* v_config_403_, lean_object* v_s_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_401_, v_methods_402_, v_config_403_, v_s_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object* v_00_u03b1_413_, lean_object* v_x_414_, lean_object* v_methods_415_, lean_object* v_config_416_, lean_object* v_s_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Sym_Simp_SimpM_run(v_00_u03b1_413_, v_x_414_, v_methods_415_, v_config_416_, v_s_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_426_);
lean_ctor_set(v___x_428_, 3, v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object* v_x_429_, lean_object* v_methods_430_, lean_object* v_config_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_lctx_439_; lean_object* v_decls_440_; lean_object* v_size_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_lctx_439_ = lean_ctor_get(v_a_434_, 2);
v_decls_440_ = lean_ctor_get(v_lctx_439_, 1);
v_size_441_ = lean_ctor_get(v_decls_440_, 2);
v___x_442_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_441_);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v_config_431_);
lean_ctor_set(v___x_443_, 1, v_size_441_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
v___x_444_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0);
v___x_445_ = lean_st_mk_ref(v___x_444_);
lean_inc(v_a_437_);
lean_inc_ref(v_a_436_);
lean_inc(v_a_435_);
lean_inc_ref(v_a_434_);
lean_inc(v_a_433_);
lean_inc_ref(v_a_432_);
lean_inc(v___x_445_);
v___x_446_ = lean_apply_10(v_x_429_, v_methods_430_, v___x_443_, v___x_445_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, lean_box(0));
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_st_ref_get(v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_451_);
if (v_isShared_450_ == 0)
{
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_447_);
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
lean_dec(v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object* v_x_456_, lean_object* v_methods_457_, lean_object* v_config_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_456_, v_methods_457_, v_config_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object* v_00_u03b1_467_, lean_object* v_x_468_, lean_object* v_methods_469_, lean_object* v_config_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_468_, v_methods_469_, v_config_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object* v_00_u03b1_479_, lean_object* v_x_480_, lean_object* v_methods_481_, lean_object* v_config_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(v_00_u03b1_479_, v_x_480_, v_methods_481_, v_config_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object* v_a_00___x40___internal___hyg_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_00___x40___internal___hyg_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = lean_sym_simp(v_a_00___x40___internal___hyg_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object* v_a_514_){
_start:
{
lean_object* v_config_516_; lean_object* v___x_517_; 
v_config_516_ = lean_ctor_get(v_a_514_, 0);
lean_inc_ref(v_config_516_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_config_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_518_);
lean_dec_ref(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_522_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object* v_e_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_pre_554_; lean_object* v___x_555_; 
v_pre_554_ = lean_ctor_get(v_a_544_, 0);
lean_inc_ref(v_pre_554_);
lean_inc(v_a_552_);
lean_inc_ref(v_a_551_);
lean_inc(v_a_550_);
lean_inc_ref(v_a_549_);
lean_inc(v_a_548_);
lean_inc_ref(v_a_547_);
lean_inc(v_a_546_);
lean_inc_ref(v_a_545_);
lean_inc(v_a_544_);
v___x_555_ = lean_apply_11(v_pre_554_, v_e_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, lean_box(0));
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Sym_Simp_pre(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_post_579_; lean_object* v___x_580_; 
v_post_579_ = lean_ctor_get(v_a_569_, 1);
lean_inc_ref(v_post_579_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
lean_inc(v_a_575_);
lean_inc_ref(v_a_574_);
lean_inc(v_a_573_);
lean_inc_ref(v_a_572_);
lean_inc(v_a_571_);
lean_inc_ref(v_a_570_);
lean_inc(v_a_569_);
v___x_580_ = lean_apply_11(v_post_579_, v_e_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, lean_box(0));
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object* v_e_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_Sym_Simp_post(v_e_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object* v_e_595_, lean_object* v_r_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___f_599_; lean_object* v___f_600_; uint8_t v___y_602_; 
v___f_599_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_600_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
if (lean_obj_tag(v_r_596_) == 0)
{
uint8_t v_contextDependent_633_; 
v_contextDependent_633_ = lean_ctor_get_uint8(v_r_596_, 1);
v___y_602_ = v_contextDependent_633_;
goto v___jp_601_;
}
else
{
uint8_t v_contextDependent_634_; 
v_contextDependent_634_ = lean_ctor_get_uint8(v_r_596_, sizeof(void*)*2 + 1);
v___y_602_ = v_contextDependent_634_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_numSteps_604_; lean_object* v_persistentCache_605_; lean_object* v_transientCache_606_; lean_object* v_funext_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_617_; 
v___x_603_ = lean_st_ref_take(v_a_597_);
v_numSteps_604_ = lean_ctor_get(v___x_603_, 0);
v_persistentCache_605_ = lean_ctor_get(v___x_603_, 1);
v_transientCache_606_ = lean_ctor_get(v___x_603_, 2);
v_funext_607_ = lean_ctor_get(v___x_603_, 3);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_617_ == 0)
{
v___x_609_ = v___x_603_;
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_funext_607_);
lean_inc(v_transientCache_606_);
lean_inc(v_persistentCache_605_);
lean_inc(v_numSteps_604_);
lean_dec(v___x_603_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
lean_inc_ref(v_r_596_);
v___x_611_ = l_Lean_PersistentHashMap_insert___redArg(v___f_599_, v___f_600_, v_persistentCache_605_, v_e_595_, v_r_596_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_numSteps_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_transientCache_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_funext_607_);
v___x_613_ = v_reuseFailAlloc_616_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_st_ref_put(v_a_597_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_r_596_);
return v___x_615_;
}
}
}
else
{
lean_object* v___x_618_; lean_object* v_numSteps_619_; lean_object* v_persistentCache_620_; lean_object* v_transientCache_621_; lean_object* v_funext_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_632_; 
v___x_618_ = lean_st_ref_take(v_a_597_);
v_numSteps_619_ = lean_ctor_get(v___x_618_, 0);
v_persistentCache_620_ = lean_ctor_get(v___x_618_, 1);
v_transientCache_621_ = lean_ctor_get(v___x_618_, 2);
v_funext_622_ = lean_ctor_get(v___x_618_, 3);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_632_ == 0)
{
v___x_624_ = v___x_618_;
v_isShared_625_ = v_isSharedCheck_632_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_funext_622_);
lean_inc(v_transientCache_621_);
lean_inc(v_persistentCache_620_);
lean_inc(v_numSteps_619_);
lean_dec(v___x_618_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_632_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_inc_ref(v_r_596_);
v___x_626_ = l_Lean_PersistentHashMap_insert___redArg(v___f_599_, v___f_600_, v_transientCache_621_, v_e_595_, v_r_596_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_numSteps_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_persistentCache_620_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_funext_622_);
v___x_628_ = v_reuseFailAlloc_631_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_st_ref_put(v_a_597_, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_r_596_);
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object* v_e_635_, lean_object* v_r_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_Sym_Simp_cacheResult___redArg(v_e_635_, v_r_636_, v_a_637_);
lean_dec(v_a_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult(lean_object* v_e_640_, lean_object* v_r_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___f_652_; lean_object* v___f_653_; uint8_t v___y_655_; 
v___f_652_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_653_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
if (lean_obj_tag(v_r_641_) == 0)
{
uint8_t v_contextDependent_686_; 
v_contextDependent_686_ = lean_ctor_get_uint8(v_r_641_, 1);
v___y_655_ = v_contextDependent_686_;
goto v___jp_654_;
}
else
{
uint8_t v_contextDependent_687_; 
v_contextDependent_687_ = lean_ctor_get_uint8(v_r_641_, sizeof(void*)*2 + 1);
v___y_655_ = v_contextDependent_687_;
goto v___jp_654_;
}
v___jp_654_:
{
if (v___y_655_ == 0)
{
lean_object* v___x_656_; lean_object* v_numSteps_657_; lean_object* v_persistentCache_658_; lean_object* v_transientCache_659_; lean_object* v_funext_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_670_; 
v___x_656_ = lean_st_ref_take(v_a_644_);
v_numSteps_657_ = lean_ctor_get(v___x_656_, 0);
v_persistentCache_658_ = lean_ctor_get(v___x_656_, 1);
v_transientCache_659_ = lean_ctor_get(v___x_656_, 2);
v_funext_660_ = lean_ctor_get(v___x_656_, 3);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
v___x_662_ = v___x_656_;
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_funext_660_);
lean_inc(v_transientCache_659_);
lean_inc(v_persistentCache_658_);
lean_inc(v_numSteps_657_);
lean_dec(v___x_656_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc_ref(v_r_641_);
v___x_664_ = l_Lean_PersistentHashMap_insert___redArg(v___f_652_, v___f_653_, v_persistentCache_658_, v_e_640_, v_r_641_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_numSteps_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_transientCache_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_funext_660_);
v___x_666_ = v_reuseFailAlloc_669_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_st_ref_put(v_a_644_, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_r_641_);
return v___x_668_;
}
}
}
else
{
lean_object* v___x_671_; lean_object* v_numSteps_672_; lean_object* v_persistentCache_673_; lean_object* v_transientCache_674_; lean_object* v_funext_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_685_; 
v___x_671_ = lean_st_ref_take(v_a_644_);
v_numSteps_672_ = lean_ctor_get(v___x_671_, 0);
v_persistentCache_673_ = lean_ctor_get(v___x_671_, 1);
v_transientCache_674_ = lean_ctor_get(v___x_671_, 2);
v_funext_675_ = lean_ctor_get(v___x_671_, 3);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_685_ == 0)
{
v___x_677_ = v___x_671_;
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_funext_675_);
lean_inc(v_transientCache_674_);
lean_inc(v_persistentCache_673_);
lean_inc(v_numSteps_672_);
lean_dec(v___x_671_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc_ref(v_r_641_);
v___x_679_ = l_Lean_PersistentHashMap_insert___redArg(v___f_652_, v___f_653_, v_transientCache_674_, v_e_640_, v_r_641_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_numSteps_672_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_persistentCache_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_funext_675_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_st_ref_put(v_a_644_, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_r_641_);
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object* v_e_688_, lean_object* v_r_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Sym_Simp_cacheResult(v_e_688_, v_r_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object* v_a_701_, lean_object* v_persistentCache_702_, lean_object* v_transientCache_703_, lean_object* v_funext_704_, lean_object* v_a_x3f_705_){
_start:
{
lean_object* v___x_707_; lean_object* v_numSteps_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_718_; 
v___x_707_ = lean_st_ref_take(v_a_701_);
v_numSteps_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; 
v_unused_719_ = lean_ctor_get(v___x_707_, 3);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v___x_707_, 2);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v___x_707_, 1);
lean_dec(v_unused_721_);
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_numSteps_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 3, v_funext_704_);
lean_ctor_set(v___x_710_, 2, v_transientCache_703_);
lean_ctor_set(v___x_710_, 1, v_persistentCache_702_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_numSteps_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_persistentCache_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_transientCache_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_funext_704_);
v___x_714_ = v_reuseFailAlloc_717_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_st_ref_put(v_a_701_, v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_712_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object* v_a_722_, lean_object* v_persistentCache_723_, lean_object* v_transientCache_724_, lean_object* v_funext_725_, lean_object* v_a_x3f_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_722_, v_persistentCache_723_, v_transientCache_724_, v_funext_725_, v_a_x3f_726_);
lean_dec(v_a_x3f_726_);
lean_dec(v_a_722_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object* v_k_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; lean_object* v_persistentCache_741_; lean_object* v___x_742_; lean_object* v_transientCache_743_; lean_object* v___x_744_; lean_object* v_funext_745_; lean_object* v_r_746_; 
v___x_740_ = lean_st_ref_get(v_a_732_);
v_persistentCache_741_ = lean_ctor_get(v___x_740_, 1);
lean_inc_ref(v_persistentCache_741_);
lean_dec(v___x_740_);
v___x_742_ = lean_st_ref_get(v_a_732_);
v_transientCache_743_ = lean_ctor_get(v___x_742_, 2);
lean_inc_ref(v_transientCache_743_);
lean_dec(v___x_742_);
v___x_744_ = lean_st_ref_get(v_a_732_);
v_funext_745_ = lean_ctor_get(v___x_744_, 3);
lean_inc_ref(v_funext_745_);
lean_dec(v___x_744_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc(v_a_732_);
lean_inc_ref(v_a_731_);
lean_inc(v_a_730_);
v_r_746_ = lean_apply_10(v_k_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, lean_box(0));
if (lean_obj_tag(v_r_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_763_; 
v_a_747_ = lean_ctor_get(v_r_746_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_r_746_);
if (v_isSharedCheck_763_ == 0)
{
v___x_749_ = v_r_746_;
v_isShared_750_ = v_isSharedCheck_763_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v_r_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_763_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
lean_inc(v_a_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 1);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_762_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v___x_753_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_732_, v_persistentCache_741_, v_transientCache_743_, v_funext_745_, v___x_752_);
lean_dec_ref(v___x_752_);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_761_);
v___x_755_ = v___x_753_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_a_747_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_747_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_764_ = lean_ctor_get(v_r_746_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v_r_746_, 1);
v___x_765_ = lean_box(0);
v___x_766_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_732_, v_persistentCache_741_, v_transientCache_743_, v_funext_745_, v___x_765_);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v___x_766_, 0);
lean_dec(v_unused_774_);
v___x_768_ = v___x_766_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_dec(v___x_766_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 0, v_a_764_);
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_764_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object* v_k_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object* v_00_u03b1_787_, lean_object* v_k_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; lean_object* v_persistentCache_800_; lean_object* v___x_801_; lean_object* v_transientCache_802_; lean_object* v___x_803_; lean_object* v_funext_804_; lean_object* v_r_805_; 
v___x_799_ = lean_st_ref_get(v_a_791_);
v_persistentCache_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc_ref(v_persistentCache_800_);
lean_dec(v___x_799_);
v___x_801_ = lean_st_ref_get(v_a_791_);
v_transientCache_802_ = lean_ctor_get(v___x_801_, 2);
lean_inc_ref(v_transientCache_802_);
lean_dec(v___x_801_);
v___x_803_ = lean_st_ref_get(v_a_791_);
v_funext_804_ = lean_ctor_get(v___x_803_, 3);
lean_inc_ref(v_funext_804_);
lean_dec(v___x_803_);
lean_inc(v_a_797_);
lean_inc_ref(v_a_796_);
lean_inc(v_a_795_);
lean_inc_ref(v_a_794_);
lean_inc(v_a_793_);
lean_inc_ref(v_a_792_);
lean_inc(v_a_791_);
lean_inc_ref(v_a_790_);
lean_inc(v_a_789_);
v_r_805_ = lean_apply_10(v_k_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, lean_box(0));
if (lean_obj_tag(v_r_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_822_; 
v_a_806_ = lean_ctor_get(v_r_805_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_r_805_);
if (v_isSharedCheck_822_ == 0)
{
v___x_808_ = v_r_805_;
v_isShared_809_ = v_isSharedCheck_822_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v_r_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_822_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
lean_inc(v_a_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 1);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_821_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v___x_812_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_791_, v_persistentCache_800_, v_transientCache_802_, v_funext_804_, v___x_811_);
lean_dec_ref(v___x_811_);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_820_);
v___x_814_ = v___x_812_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v_a_806_);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_806_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
v_a_823_ = lean_ctor_get(v_r_805_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v_r_805_, 1);
v___x_824_ = lean_box(0);
v___x_825_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_791_, v_persistentCache_800_, v_transientCache_802_, v_funext_804_, v___x_824_);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_825_, 0);
lean_dec(v_unused_833_);
v___x_827_ = v___x_825_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_dec(v___x_825_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v_a_823_);
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_823_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object* v_00_u03b1_834_, lean_object* v_k_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(v_00_u03b1_834_, v_k_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(lean_object* v_a_847_, lean_object* v_transientCache_848_, lean_object* v_funext_849_, lean_object* v_a_x3f_850_){
_start:
{
lean_object* v___x_852_; lean_object* v_numSteps_853_; lean_object* v_persistentCache_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v___x_852_ = lean_st_ref_take(v_a_847_);
v_numSteps_853_ = lean_ctor_get(v___x_852_, 0);
v_persistentCache_854_ = lean_ctor_get(v___x_852_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; 
v_unused_865_ = lean_ctor_get(v___x_852_, 3);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v___x_852_, 2);
lean_dec(v_unused_866_);
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_persistentCache_854_);
lean_inc(v_numSteps_853_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 3, v_funext_849_);
lean_ctor_set(v___x_856_, 2, v_transientCache_848_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_numSteps_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_persistentCache_854_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_transientCache_848_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_funext_849_);
v___x_860_ = v_reuseFailAlloc_863_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_st_ref_put(v_a_847_, v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_858_);
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(lean_object* v_a_867_, lean_object* v_transientCache_868_, lean_object* v_funext_869_, lean_object* v_a_x3f_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_867_, v_transientCache_868_, v_funext_869_, v_a_x3f_870_);
lean_dec(v_a_x3f_870_);
lean_dec(v_a_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(lean_object* v_k_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_transientCache_885_; lean_object* v___x_886_; lean_object* v_funext_887_; lean_object* v_r_888_; 
v___x_884_ = lean_st_ref_get(v_a_876_);
v_transientCache_885_ = lean_ctor_get(v___x_884_, 2);
lean_inc_ref(v_transientCache_885_);
lean_dec(v___x_884_);
v___x_886_ = lean_st_ref_get(v_a_876_);
v_funext_887_ = lean_ctor_get(v___x_886_, 3);
lean_inc_ref(v_funext_887_);
lean_dec(v___x_886_);
lean_inc(v_a_882_);
lean_inc_ref(v_a_881_);
lean_inc(v_a_880_);
lean_inc_ref(v_a_879_);
lean_inc(v_a_878_);
lean_inc_ref(v_a_877_);
lean_inc(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
v_r_888_ = lean_apply_10(v_k_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, lean_box(0));
if (lean_obj_tag(v_r_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_905_; 
v_a_889_ = lean_ctor_get(v_r_888_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_r_888_);
if (v_isSharedCheck_905_ == 0)
{
v___x_891_ = v_r_888_;
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v_r_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
lean_inc(v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 1);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_904_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v___x_895_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_876_, v_transientCache_885_, v_funext_887_, v___x_894_);
lean_dec_ref(v___x_894_);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_903_);
v___x_897_ = v___x_895_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_dec(v___x_895_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_889_);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_889_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_906_ = lean_ctor_get(v_r_888_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v_r_888_, 1);
v___x_907_ = lean_box(0);
v___x_908_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_876_, v_transientCache_885_, v_funext_887_, v___x_907_);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_916_);
v___x_910_ = v___x_908_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_dec(v___x_908_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 1);
lean_ctor_set(v___x_910_, 0, v_a_906_);
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_906_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(lean_object* v_k_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(v_k_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_object* v_00_u03b1_929_, lean_object* v_k_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_transientCache_942_; lean_object* v___x_943_; lean_object* v_funext_944_; lean_object* v_r_945_; 
v___x_941_ = lean_st_ref_get(v_a_933_);
v_transientCache_942_ = lean_ctor_get(v___x_941_, 2);
lean_inc_ref(v_transientCache_942_);
lean_dec(v___x_941_);
v___x_943_ = lean_st_ref_get(v_a_933_);
v_funext_944_ = lean_ctor_get(v___x_943_, 3);
lean_inc_ref(v_funext_944_);
lean_dec(v___x_943_);
lean_inc(v_a_939_);
lean_inc_ref(v_a_938_);
lean_inc(v_a_937_);
lean_inc_ref(v_a_936_);
lean_inc(v_a_935_);
lean_inc_ref(v_a_934_);
lean_inc(v_a_933_);
lean_inc_ref(v_a_932_);
lean_inc(v_a_931_);
v_r_945_ = lean_apply_10(v_k_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, lean_box(0));
if (lean_obj_tag(v_r_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_962_; 
v_a_946_ = lean_ctor_get(v_r_945_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_r_945_);
if (v_isSharedCheck_962_ == 0)
{
v___x_948_ = v_r_945_;
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v_r_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
lean_inc(v_a_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 1);
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_961_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v___x_952_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_933_, v_transientCache_942_, v_funext_944_, v___x_951_);
lean_dec_ref(v___x_951_);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_960_);
v___x_954_ = v___x_952_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_952_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_a_946_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_946_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_963_ = lean_ctor_get(v_r_945_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v_r_945_, 1);
v___x_964_ = lean_box(0);
v___x_965_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_933_, v_transientCache_942_, v_funext_944_, v___x_964_);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v___x_965_, 0);
lean_dec(v_unused_973_);
v___x_967_ = v___x_965_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_dec(v___x_965_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 1);
lean_ctor_set(v___x_967_, 0, v_a_963_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_963_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(lean_object* v_00_u03b1_974_, lean_object* v_k_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(v_00_u03b1_974_, v_k_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp(lean_object* v_e_987_, lean_object* v_methods_988_, lean_object* v_config_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_997_, 0, v_e_987_);
v___x_998_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_997_, v_methods_988_, v_config_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object* v_e_999_, lean_object* v_methods_1000_, lean_object* v_config_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_Sym_simp(v_e_999_, v_methods_1000_, v_config_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1009_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
