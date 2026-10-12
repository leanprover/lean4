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
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t v_done_56_, uint8_t v_contextDependent_57_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkRflResult_0interp(lean_interpreter_value* stack)
{
uint8_t v_done_56_ = stack[0].m_num;
uint8_t v_contextDependent_57_ = stack[1].m_num;
lean_object* v_res_62_;
v_res_62_ = l_Lean_Meta_Sym_Simp_mkRflResult(v_done_56_, v_contextDependent_57_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResult___boxed(lean_object* v_done_63_, lean_object* v_contextDependent_64_){
_start:
{
uint8_t v_done_boxed_65_; uint8_t v_contextDependent_boxed_66_; lean_object* v_res_67_; 
v_done_boxed_65_ = lean_unbox(v_done_63_);
v_contextDependent_boxed_66_ = lean_unbox(v_contextDependent_64_);
v_res_67_ = l_Lean_Meta_Sym_Simp_mkRflResult(v_done_boxed_65_, v_contextDependent_boxed_66_);
return v_res_67_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t v_contextDependent_68_){
_start:
{
if (v_contextDependent_68_ == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_69_, 0, v_contextDependent_68_);
lean_ctor_set_uint8(v___x_69_, 1, v_contextDependent_68_);
return v___x_69_;
}
else
{
uint8_t v___x_70_; lean_object* v___x_71_; 
v___x_70_ = 0;
v___x_71_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_71_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_71_, 1, v_contextDependent_68_);
return v___x_71_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkRflResultCD_0interp(lean_interpreter_value* stack)
{
uint8_t v_contextDependent_68_ = stack[0].m_num;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_68_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD___boxed(lean_object* v_contextDependent_73_){
_start:
{
uint8_t v_contextDependent_boxed_74_; lean_object* v_res_75_; 
v_contextDependent_boxed_74_ = lean_unbox(v_contextDependent_73_);
v_res_75_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_boxed_74_);
return v_res_75_;
}
}
uint8_t l_Lean_Meta_Sym_Simp_Result_isContextDependent(lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
uint8_t v_contextDependent_77_; 
v_contextDependent_77_ = lean_ctor_get_uint8(v_x_76_, 1);
return v_contextDependent_77_;
}
else
{
uint8_t v_contextDependent_78_; 
v_contextDependent_78_ = lean_ctor_get_uint8(v_x_76_, sizeof(void*)*2 + 1);
return v_contextDependent_78_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Result_isContextDependent_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_76_ = stack[0].m_obj;
uint8_t v_res_79_;
v_res_79_ = l_Lean_Meta_Sym_Simp_Result_isContextDependent(v_x_76_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isContextDependent___boxed(lean_object* v_x_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_Meta_Sym_Simp_Result_isContextDependent(v_x_80_);
lean_dec_ref(v_x_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
uint8_t v_done_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_done_84_ = lean_ctor_get_uint8(v_x_83_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v_x_83_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_dec(v_x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v___x_88_; lean_object* v___x_90_; 
v___x_88_ = 1;
if (v_isShared_87_ == 0)
{
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_91_, 0, v_done_84_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_ctor_set_uint8(v___x_90_, 1, v___x_88_);
return v___x_90_;
}
}
}
else
{
lean_object* v_e_x27_93_; lean_object* v_proof_94_; uint8_t v_done_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_103_; 
v_e_x27_93_ = lean_ctor_get(v_x_83_, 0);
v_proof_94_ = lean_ctor_get(v_x_83_, 1);
v_done_95_ = lean_ctor_get_uint8(v_x_83_, sizeof(void*)*2);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_103_ == 0)
{
v___x_97_ = v_x_83_;
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_proof_94_);
lean_inc(v_e_x27_93_);
lean_dec(v_x_83_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
uint8_t v___x_99_; lean_object* v___x_101_; 
v___x_99_ = 1;
if (v_isShared_98_ == 0)
{
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_e_x27_93_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_proof_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*2, v_done_95_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*2 + 1, v___x_99_);
return v___x_101_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_instMonadEIO___redArg();
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__0);
v___x_107_ = l_StateRefT_x27_instMonad___redArg(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6(void){
_start:
{
lean_object* v___x_112_; lean_object* v___f_113_; 
v___x_112_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_113_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_113_, 0, v___x_112_);
return v___f_113_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7(void){
_start:
{
lean_object* v___x_114_; lean_object* v___f_115_; 
v___x_114_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_115_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_115_, 0, v___x_114_);
return v___f_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8(void){
_start:
{
lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_118_; 
v___f_116_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__7);
v___f_117_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__6);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___f_117_);
lean_ctor_set(v___x_118_, 1, v___f_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9(void){
_start:
{
lean_object* v___x_119_; lean_object* v___f_120_; 
v___x_119_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8);
v___f_120_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_120_, 0, v___x_119_);
return v___f_120_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10(void){
_start:
{
lean_object* v___x_121_; lean_object* v___f_122_; 
v___x_121_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__8);
v___f_122_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_122_, 0, v___x_121_);
return v___f_122_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11(void){
_start:
{
lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; 
v___f_123_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__10);
v___f_124_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__9);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___f_124_);
lean_ctor_set(v___x_125_, 1, v___f_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12(void){
_start:
{
lean_object* v___x_126_; lean_object* v___f_127_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11);
v___f_127_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_127_, 0, v___x_126_);
return v___f_127_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13(void){
_start:
{
lean_object* v___x_128_; lean_object* v___f_129_; 
v___x_128_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__11);
v___f_129_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_129_, 0, v___x_128_);
return v___f_129_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14(void){
_start:
{
lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v___f_130_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__13);
v___f_131_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__12);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___f_131_);
lean_ctor_set(v___x_132_, 1, v___f_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15(void){
_start:
{
lean_object* v___x_133_; lean_object* v___f_134_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_134_, 0, v___x_133_);
return v___f_134_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16(void){
_start:
{
lean_object* v___x_135_; lean_object* v___f_136_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__14);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
return v___f_136_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17(void){
_start:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v___f_137_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__16);
v___f_138_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__15);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___f_138_);
lean_ctor_set(v___x_139_, 1, v___f_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18(void){
_start:
{
lean_object* v___x_140_; lean_object* v___f_141_; 
v___x_140_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17);
v___f_141_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_141_, 0, v___x_140_);
return v___f_141_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19(void){
_start:
{
lean_object* v___x_142_; lean_object* v___f_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__17);
v___f_143_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_143_, 0, v___x_142_);
return v___f_143_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20(void){
_start:
{
lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v___f_144_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__19);
v___f_145_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__18);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_145_);
lean_ctor_set(v___x_146_, 1, v___f_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21(void){
_start:
{
lean_object* v___x_147_; lean_object* v___f_148_; 
v___x_147_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_148_, 0, v___x_147_);
return v___f_148_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22(void){
_start:
{
lean_object* v___x_149_; lean_object* v___f_150_; 
v___x_149_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__20);
v___f_150_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_150_, 0, v___x_149_);
return v___f_150_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23(void){
_start:
{
lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_153_; 
v___f_151_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__22);
v___f_152_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__21);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___f_152_);
lean_ctor_set(v___x_153_, 1, v___f_151_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24(void){
_start:
{
lean_object* v___x_154_; lean_object* v___f_155_; 
v___x_154_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_155_, 0, v___x_154_);
return v___f_155_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25(void){
_start:
{
lean_object* v___x_156_; lean_object* v___f_157_; 
v___x_156_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__23);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_157_, 0, v___x_156_);
return v___f_157_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26(void){
_start:
{
lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; 
v___f_158_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__25);
v___f_159_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__24);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___f_159_);
lean_ctor_set(v___x_160_, 1, v___f_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_166_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_167_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29));
v___x_168_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_167_, v___x_166_, v___x_165_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32(void){
_start:
{
lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_172_; 
v___x_169_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__31);
v___f_170_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_171_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_172_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_171_, v___f_170_, v___x_169_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__32);
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_175_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29));
v___x_176_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_175_, v___x_174_, v___x_173_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34(void){
_start:
{
lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; 
v___x_177_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__33);
v___f_178_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_179_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_180_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_179_, v___f_178_, v___x_177_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__34);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_183_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__29));
v___x_184_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_183_, v___x_182_, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36(void){
_start:
{
lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___x_188_; 
v___x_185_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__35);
v___f_186_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_187_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_188_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_187_, v___f_186_, v___x_185_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37(void){
_start:
{
lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__36);
v___f_190_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_191_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__27));
v___x_192_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_191_, v___f_190_, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___f_195_; 
v___x_193_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___x_194_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_195_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_195_, 0, v___x_194_);
lean_closure_set(v___f_195_, 1, v___x_193_);
return v___f_195_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39(void){
_start:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; 
v___f_196_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_197_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__38);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_198_, 0, v___f_197_);
lean_closure_set(v___f_198_, 1, v___f_196_);
return v___f_198_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40(void){
_start:
{
lean_object* v___x_199_; lean_object* v___f_200_; lean_object* v___f_201_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__30));
v___f_200_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__39);
v___f_201_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_201_, 0, v___f_200_);
lean_closure_set(v___f_201_, 1, v___x_199_);
return v___f_201_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41(void){
_start:
{
lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; 
v___f_202_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_203_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__40);
v___f_204_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_204_, 0, v___f_203_);
lean_closure_set(v___f_204_, 1, v___f_202_);
return v___f_204_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42(void){
_start:
{
lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; 
v___f_205_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__28));
v___f_206_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__41);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_207_, 0, v___f_206_);
lean_closure_set(v___f_207_, 1, v___f_205_);
return v___f_207_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__43));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg(){
_start:
{
lean_object* v___x_212_; lean_object* v_toApplicative_213_; lean_object* v_toFunctor_214_; lean_object* v_toSeq_215_; lean_object* v_toSeqLeft_216_; lean_object* v_toSeqRight_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_toApplicative_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_269_; 
v___x_212_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__1);
v_toApplicative_213_ = lean_ctor_get(v___x_212_, 0);
v_toFunctor_214_ = lean_ctor_get(v_toApplicative_213_, 0);
v_toSeq_215_ = lean_ctor_get(v_toApplicative_213_, 2);
v_toSeqLeft_216_ = lean_ctor_get(v_toApplicative_213_, 3);
v_toSeqRight_217_ = lean_ctor_get(v_toApplicative_213_, 4);
v___f_218_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__2));
v___f_219_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_214_, 2);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_220_, 0, v_toFunctor_214_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_221_, 0, v_toFunctor_214_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___f_220_);
lean_ctor_set(v___x_222_, 1, v___f_221_);
lean_inc(v_toSeqRight_217_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_223_, 0, v_toSeqRight_217_);
lean_inc(v_toSeqLeft_216_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_224_, 0, v_toSeqLeft_216_);
lean_inc(v_toSeq_215_);
v___f_225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_225_, 0, v_toSeq_215_);
v___x_226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_226_, 0, v___x_222_);
lean_ctor_set(v___x_226_, 1, v___f_218_);
lean_ctor_set(v___x_226_, 2, v___f_225_);
lean_ctor_set(v___x_226_, 3, v___f_224_);
lean_ctor_set(v___x_226_, 4, v___f_223_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___f_219_);
v___x_228_ = l_StateRefT_x27_instMonad___redArg(v___x_227_);
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
v___f_240_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__4));
v___f_241_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__5));
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
v___x_252_ = l_StateRefT_x27_instMonad___redArg(v___x_251_);
v___x_253_ = l_ReaderT_instMonad___redArg(v___x_252_);
v___x_254_ = l_StateRefT_x27_instMonad___redArg(v___x_253_);
v___x_255_ = l_ReaderT_instMonad___redArg(v___x_254_);
v___x_256_ = l_ReaderT_instMonad___redArg(v___x_255_);
v___x_257_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__26);
v___x_258_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__37);
v_toMonadRef_259_ = lean_ctor_get(v___x_258_, 0);
v___f_260_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__42);
lean_inc_ref(v___x_256_);
v___x_261_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_260_, v___x_256_);
lean_inc_ref(v_toMonadRef_259_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_257_);
lean_ctor_set(v___x_262_, 1, v_toMonadRef_259_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___closed__44);
v___x_264_ = l_Lean_throwError___redArg(v___x_256_, v___x_262_, v___x_263_);
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_271_;
v_res_271_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg___boxed(lean_object* v___dummy_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v_res_273_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object* v_00_u03b1_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0);
return v___x_276_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0));
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_277_ = stack[0].m_obj;
lean_object* v___y_278_ = stack[1].m_obj;
lean_object* v___y_279_ = stack[2].m_obj;
lean_object* v___y_280_ = stack[3].m_obj;
lean_object* v___y_281_ = stack[4].m_obj;
lean_object* v___y_282_ = stack[5].m_obj;
lean_object* v___y_283_ = stack[6].m_obj;
lean_object* v___y_284_ = stack[7].m_obj;
lean_object* v___y_285_ = stack[8].m_obj;
lean_object* v___y_286_ = stack[9].m_obj;
lean_object* v_res_290_;
v_res_290_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v_x_291_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(lean_object* v_m_308_){
_start:
{
lean_inc_ref(v_m_308_);
return v_m_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_309_);
lean_dec_ref(v_m_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(lean_object* v_m_311_){
_start:
{
lean_inc(v_m_311_);
return v_m_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_312_);
lean_dec(v_m_312_);
return v_res_313_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg(lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
lean_inc(v_a_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v_a_314_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_getMethods___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_314_ = stack[0].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_314_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_318_);
lean_dec(v_a_318_);
return v_res_320_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_getMethods(lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v_a_321_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_a_321_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_getMethods_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_321_ = stack[0].m_obj;
lean_object* v_a_322_ = stack[1].m_obj;
lean_object* v_a_323_ = stack[2].m_obj;
lean_object* v_a_324_ = stack[3].m_obj;
lean_object* v_a_325_ = stack[4].m_obj;
lean_object* v_a_326_ = stack[5].m_obj;
lean_object* v_a_327_ = stack[6].m_obj;
lean_object* v_a_328_ = stack[7].m_obj;
lean_object* v_a_329_ = stack[8].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getMethods___boxed(lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Sym_Simp_getMethods(v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object* v_x_347_, lean_object* v_methods_348_, lean_object* v_config_349_, lean_object* v_s_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_lctx_358_; lean_object* v_decls_359_; lean_object* v_size_360_; lean_object* v_persistentCache_361_; lean_object* v_funext_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_392_; 
v_lctx_358_ = lean_ctor_get(v_a_353_, 2);
v_decls_359_ = lean_ctor_get(v_lctx_358_, 1);
v_size_360_ = lean_ctor_get(v_decls_359_, 2);
v_persistentCache_361_ = lean_ctor_get(v_s_350_, 1);
v_funext_362_ = lean_ctor_get(v_s_350_, 3);
v_isSharedCheck_392_ = !lean_is_exclusive(v_s_350_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; lean_object* v_unused_394_; 
v_unused_393_ = lean_ctor_get(v_s_350_, 2);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_s_350_, 0);
lean_dec(v_unused_394_);
v___x_364_ = v_s_350_;
v_isShared_365_ = v_isSharedCheck_392_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_funext_362_);
lean_inc(v_persistentCache_361_);
lean_dec(v_s_350_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_392_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_366_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_360_);
v___x_367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_367_, 0, v_config_349_);
lean_ctor_set(v___x_367_, 1, v_size_360_);
lean_ctor_set(v___x_367_, 2, v___x_366_);
v___x_368_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v___x_368_);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_370_ = v___x_364_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_persistentCache_361_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_funext_362_);
v___x_370_ = v_reuseFailAlloc_391_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_st_mk_ref(v___x_370_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
lean_inc(v___x_371_);
v___x_372_ = lean_apply_10(v_x_347_, v_methods_348_, v___x_367_, v___x_371_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, lean_box(0));
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_382_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = lean_st_ref_get(v___x_371_);
lean_dec(v___x_371_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_a_373_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
if (v_isShared_376_ == 0)
{
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
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v___x_371_);
v_a_383_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_372_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_372_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_SimpM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_347_ = stack[0].m_obj;
lean_object* v_methods_348_ = stack[1].m_obj;
lean_object* v_config_349_ = stack[2].m_obj;
lean_object* v_s_350_ = stack[3].m_obj;
lean_object* v_a_351_ = stack[4].m_obj;
lean_object* v_a_352_ = stack[5].m_obj;
lean_object* v_a_353_ = stack[6].m_obj;
lean_object* v_a_354_ = stack[7].m_obj;
lean_object* v_a_355_ = stack[8].m_obj;
lean_object* v_a_356_ = stack[9].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_347_, v_methods_348_, v_config_349_, v_s_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(lean_object* v_x_396_, lean_object* v_methods_397_, lean_object* v_config_398_, lean_object* v_s_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_396_, v_methods_397_, v_config_398_, v_s_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_407_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run(lean_object* v_00_u03b1_408_, lean_object* v_x_409_, lean_object* v_methods_410_, lean_object* v_config_411_, lean_object* v_s_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_x_409_, v_methods_410_, v_config_411_, v_s_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_SimpM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_409_ = stack[1].m_obj;
lean_object* v_methods_410_ = stack[2].m_obj;
lean_object* v_config_411_ = stack[3].m_obj;
lean_object* v_s_412_ = stack[4].m_obj;
lean_object* v_a_413_ = stack[5].m_obj;
lean_object* v_a_414_ = stack[6].m_obj;
lean_object* v_a_415_ = stack[7].m_obj;
lean_object* v_a_416_ = stack[8].m_obj;
lean_object* v_a_417_ = stack[9].m_obj;
lean_object* v_a_418_ = stack[10].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Meta_Sym_Simp_SimpM_run(lean_box(0), v_x_409_, v_methods_410_, v_config_411_, v_s_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___boxed(lean_object* v_00_u03b1_422_, lean_object* v_x_423_, lean_object* v_methods_424_, lean_object* v_config_425_, lean_object* v_s_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_Sym_Simp_SimpM_run(v_00_u03b1_422_, v_x_423_, v_methods_424_, v_config_425_, v_s_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_434_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_435_);
lean_ctor_set(v___x_437_, 3, v___x_435_);
return v___x_437_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object* v_x_438_, lean_object* v_methods_439_, lean_object* v_config_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_lctx_448_; lean_object* v_decls_449_; lean_object* v_size_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_lctx_448_ = lean_ctor_get(v_a_443_, 2);
v_decls_449_ = lean_ctor_get(v_lctx_448_, 1);
v_size_450_ = lean_ctor_get(v_decls_449_, 2);
v___x_451_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_450_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v_config_440_);
lean_ctor_set(v___x_452_, 1, v_size_450_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
v___x_453_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0);
v___x_454_ = lean_st_mk_ref(v___x_453_);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc_ref(v_a_443_);
lean_inc(v_a_442_);
lean_inc_ref(v_a_441_);
lean_inc(v___x_454_);
v___x_455_ = lean_apply_10(v_x_438_, v_methods_439_, v___x_452_, v___x_454_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, lean_box(0));
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_st_ref_get(v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_460_);
if (v_isShared_459_ == 0)
{
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_dec(v___x_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_438_ = stack[0].m_obj;
lean_object* v_methods_439_ = stack[1].m_obj;
lean_object* v_config_440_ = stack[2].m_obj;
lean_object* v_a_441_ = stack[3].m_obj;
lean_object* v_a_442_ = stack[4].m_obj;
lean_object* v_a_443_ = stack[5].m_obj;
lean_object* v_a_444_ = stack[6].m_obj;
lean_object* v_a_445_ = stack[7].m_obj;
lean_object* v_a_446_ = stack[8].m_obj;
lean_object* v_res_465_;
v_res_465_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_438_, v_methods_439_, v_config_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(lean_object* v_x_466_, lean_object* v_methods_467_, lean_object* v_config_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_466_, v_methods_467_, v_config_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
return v_res_476_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_object* v_00_u03b1_477_, lean_object* v_x_478_, lean_object* v_methods_479_, lean_object* v_config_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v_x_478_, v_methods_479_, v_config_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_488_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_SimpM_run_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_478_ = stack[1].m_obj;
lean_object* v_methods_479_ = stack[2].m_obj;
lean_object* v_config_480_ = stack[3].m_obj;
lean_object* v_a_481_ = stack[4].m_obj;
lean_object* v_a_482_ = stack[5].m_obj;
lean_object* v_a_483_ = stack[6].m_obj;
lean_object* v_a_484_ = stack[7].m_obj;
lean_object* v_a_485_ = stack[8].m_obj;
lean_object* v_a_486_ = stack[9].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(lean_box(0), v_x_478_, v_methods_479_, v_config_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(lean_object* v_00_u03b1_490_, lean_object* v_x_491_, lean_object* v_methods_492_, lean_object* v_config_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(v_00_u03b1_490_, v_x_491_, v_methods_492_, v_config_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
return v_res_501_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_502_ = stack[0].m_obj;
lean_object* v_a_503_ = stack[1].m_obj;
lean_object* v_a_504_ = stack[2].m_obj;
lean_object* v_a_505_ = stack[3].m_obj;
lean_object* v_a_506_ = stack[4].m_obj;
lean_object* v_a_507_ = stack[5].m_obj;
lean_object* v_a_508_ = stack[6].m_obj;
lean_object* v_a_509_ = stack[7].m_obj;
lean_object* v_a_510_ = stack[8].m_obj;
lean_object* v_a_511_ = stack[9].m_obj;
lean_object* v_res_513_;
v_res_513_ = lean_sym_simp(v_a_00___x40___internal___hyg_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object* v_a_00___x40___internal___hyg_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_00___x40___internal___hyg_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = lean_sym_simp(v_a_00___x40___internal___hyg_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v_res_525_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object* v_a_526_){
_start:
{
lean_object* v_config_528_; lean_object* v___x_529_; 
v_config_528_ = lean_ctor_get(v_a_526_, 0);
lean_inc_ref(v_config_528_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v_config_528_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_getConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_526_ = stack[0].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_526_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_531_);
lean_dec_ref(v_a_531_);
return v_res_533_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_getConfig(lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_535_);
return v___x_544_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_getConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_534_ = stack[0].m_obj;
lean_object* v_a_535_ = stack[1].m_obj;
lean_object* v_a_536_ = stack[2].m_obj;
lean_object* v_a_537_ = stack[3].m_obj;
lean_object* v_a_538_ = stack[4].m_obj;
lean_object* v_a_539_ = stack[5].m_obj;
lean_object* v_a_540_ = stack[6].m_obj;
lean_object* v_a_541_ = stack[7].m_obj;
lean_object* v_a_542_ = stack[8].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getConfig___boxed(lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Sym_Simp_getConfig(v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
return v_res_556_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_pre(lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_pre_568_; lean_object* v___x_569_; 
v_pre_568_ = lean_ctor_get(v_a_558_, 0);
lean_inc_ref(v_pre_568_);
lean_inc(v_a_566_);
lean_inc_ref(v_a_565_);
lean_inc(v_a_564_);
lean_inc_ref(v_a_563_);
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
lean_inc(v_a_558_);
v___x_569_ = lean_apply_11(v_pre_568_, v_e_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, lean_box(0));
return v___x_569_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_pre_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_557_ = stack[0].m_obj;
lean_object* v_a_558_ = stack[1].m_obj;
lean_object* v_a_559_ = stack[2].m_obj;
lean_object* v_a_560_ = stack[3].m_obj;
lean_object* v_a_561_ = stack[4].m_obj;
lean_object* v_a_562_ = stack[5].m_obj;
lean_object* v_a_563_ = stack[6].m_obj;
lean_object* v_a_564_ = stack[7].m_obj;
lean_object* v_a_565_ = stack[8].m_obj;
lean_object* v_a_566_ = stack[9].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_Lean_Meta_Sym_Simp_pre(v_e_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pre___boxed(lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_Sym_Simp_pre(v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
return v_res_582_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_post(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_post_594_; lean_object* v___x_595_; 
v_post_594_ = lean_ctor_get(v_a_584_, 1);
lean_inc_ref(v_post_594_);
lean_inc(v_a_592_);
lean_inc_ref(v_a_591_);
lean_inc(v_a_590_);
lean_inc_ref(v_a_589_);
lean_inc(v_a_588_);
lean_inc_ref(v_a_587_);
lean_inc(v_a_586_);
lean_inc_ref(v_a_585_);
lean_inc(v_a_584_);
v___x_595_ = lean_apply_11(v_post_594_, v_e_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, lean_box(0));
return v___x_595_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_post_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_583_ = stack[0].m_obj;
lean_object* v_a_584_ = stack[1].m_obj;
lean_object* v_a_585_ = stack[2].m_obj;
lean_object* v_a_586_ = stack[3].m_obj;
lean_object* v_a_587_ = stack[4].m_obj;
lean_object* v_a_588_ = stack[5].m_obj;
lean_object* v_a_589_ = stack[6].m_obj;
lean_object* v_a_590_ = stack[7].m_obj;
lean_object* v_a_591_ = stack[8].m_obj;
lean_object* v_a_592_ = stack[9].m_obj;
lean_object* v_res_596_;
v_res_596_ = l_Lean_Meta_Sym_Simp_post(v_e_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_post___boxed(lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Meta_Sym_Simp_post(v_e_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
return v_res_608_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object* v_e_611_, lean_object* v_r_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___f_615_; lean_object* v___f_616_; uint8_t v___y_618_; 
v___f_615_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_616_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
if (lean_obj_tag(v_r_612_) == 0)
{
uint8_t v_contextDependent_649_; 
v_contextDependent_649_ = lean_ctor_get_uint8(v_r_612_, 1);
v___y_618_ = v_contextDependent_649_;
goto v___jp_617_;
}
else
{
uint8_t v_contextDependent_650_; 
v_contextDependent_650_ = lean_ctor_get_uint8(v_r_612_, sizeof(void*)*2 + 1);
v___y_618_ = v_contextDependent_650_;
goto v___jp_617_;
}
v___jp_617_:
{
if (v___y_618_ == 0)
{
lean_object* v___x_619_; lean_object* v_numSteps_620_; lean_object* v_persistentCache_621_; lean_object* v_transientCache_622_; lean_object* v_funext_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_633_; 
v___x_619_ = lean_st_ref_take(v_a_613_);
v_numSteps_620_ = lean_ctor_get(v___x_619_, 0);
v_persistentCache_621_ = lean_ctor_get(v___x_619_, 1);
v_transientCache_622_ = lean_ctor_get(v___x_619_, 2);
v_funext_623_ = lean_ctor_get(v___x_619_, 3);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_633_ == 0)
{
v___x_625_ = v___x_619_;
v_isShared_626_ = v_isSharedCheck_633_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_funext_623_);
lean_inc(v_transientCache_622_);
lean_inc(v_persistentCache_621_);
lean_inc(v_numSteps_620_);
lean_dec(v___x_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_633_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
lean_inc_ref(v_r_612_);
v___x_627_ = l_Lean_PersistentHashMap_insert___redArg(v___f_615_, v___f_616_, v_persistentCache_621_, v_e_611_, v_r_612_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_numSteps_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_transientCache_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_funext_623_);
v___x_629_ = v_reuseFailAlloc_632_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_st_ref_put(v_a_613_, v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_r_612_);
return v___x_631_;
}
}
}
else
{
lean_object* v___x_634_; lean_object* v_numSteps_635_; lean_object* v_persistentCache_636_; lean_object* v_transientCache_637_; lean_object* v_funext_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_648_; 
v___x_634_ = lean_st_ref_take(v_a_613_);
v_numSteps_635_ = lean_ctor_get(v___x_634_, 0);
v_persistentCache_636_ = lean_ctor_get(v___x_634_, 1);
v_transientCache_637_ = lean_ctor_get(v___x_634_, 2);
v_funext_638_ = lean_ctor_get(v___x_634_, 3);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_648_ == 0)
{
v___x_640_ = v___x_634_;
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_funext_638_);
lean_inc(v_transientCache_637_);
lean_inc(v_persistentCache_636_);
lean_inc(v_numSteps_635_);
lean_dec(v___x_634_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
lean_inc_ref(v_r_612_);
v___x_642_ = l_Lean_PersistentHashMap_insert___redArg(v___f_615_, v___f_616_, v_transientCache_637_, v_e_611_, v_r_612_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_numSteps_635_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_persistentCache_636_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_funext_638_);
v___x_644_ = v_reuseFailAlloc_647_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_st_ref_put(v_a_613_, v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_r_612_);
return v___x_646_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_cacheResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_611_ = stack[0].m_obj;
lean_object* v_r_612_ = stack[1].m_obj;
lean_object* v_a_613_ = stack[2].m_obj;
lean_object* v_res_651_;
v_res_651_ = l_Lean_Meta_Sym_Simp_cacheResult___redArg(v_e_611_, v_r_612_, v_a_613_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object* v_e_652_, lean_object* v_r_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Sym_Simp_cacheResult___redArg(v_e_652_, v_r_653_, v_a_654_);
lean_dec(v_a_654_);
return v_res_656_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_cacheResult(lean_object* v_e_657_, lean_object* v_r_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___f_669_; lean_object* v___f_670_; uint8_t v___y_672_; 
v___f_669_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_670_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
if (lean_obj_tag(v_r_658_) == 0)
{
uint8_t v_contextDependent_703_; 
v_contextDependent_703_ = lean_ctor_get_uint8(v_r_658_, 1);
v___y_672_ = v_contextDependent_703_;
goto v___jp_671_;
}
else
{
uint8_t v_contextDependent_704_; 
v_contextDependent_704_ = lean_ctor_get_uint8(v_r_658_, sizeof(void*)*2 + 1);
v___y_672_ = v_contextDependent_704_;
goto v___jp_671_;
}
v___jp_671_:
{
if (v___y_672_ == 0)
{
lean_object* v___x_673_; lean_object* v_numSteps_674_; lean_object* v_persistentCache_675_; lean_object* v_transientCache_676_; lean_object* v_funext_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_687_; 
v___x_673_ = lean_st_ref_take(v_a_661_);
v_numSteps_674_ = lean_ctor_get(v___x_673_, 0);
v_persistentCache_675_ = lean_ctor_get(v___x_673_, 1);
v_transientCache_676_ = lean_ctor_get(v___x_673_, 2);
v_funext_677_ = lean_ctor_get(v___x_673_, 3);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_687_ == 0)
{
v___x_679_ = v___x_673_;
v_isShared_680_ = v_isSharedCheck_687_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_funext_677_);
lean_inc(v_transientCache_676_);
lean_inc(v_persistentCache_675_);
lean_inc(v_numSteps_674_);
lean_dec(v___x_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_687_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
lean_inc_ref(v_r_658_);
v___x_681_ = l_Lean_PersistentHashMap_insert___redArg(v___f_669_, v___f_670_, v_persistentCache_675_, v_e_657_, v_r_658_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_numSteps_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_transientCache_676_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_funext_677_);
v___x_683_ = v_reuseFailAlloc_686_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_st_ref_put(v_a_661_, v___x_683_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_r_658_);
return v___x_685_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v_numSteps_689_; lean_object* v_persistentCache_690_; lean_object* v_transientCache_691_; lean_object* v_funext_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
v___x_688_ = lean_st_ref_take(v_a_661_);
v_numSteps_689_ = lean_ctor_get(v___x_688_, 0);
v_persistentCache_690_ = lean_ctor_get(v___x_688_, 1);
v_transientCache_691_ = lean_ctor_get(v___x_688_, 2);
v_funext_692_ = lean_ctor_get(v___x_688_, 3);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_702_ == 0)
{
v___x_694_ = v___x_688_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_funext_692_);
lean_inc(v_transientCache_691_);
lean_inc(v_persistentCache_690_);
lean_inc(v_numSteps_689_);
lean_dec(v___x_688_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_inc_ref(v_r_658_);
v___x_696_ = l_Lean_PersistentHashMap_insert___redArg(v___f_669_, v___f_670_, v_transientCache_691_, v_e_657_, v_r_658_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 2, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_numSteps_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_persistentCache_690_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_funext_692_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_st_ref_put(v_a_661_, v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v_r_658_);
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_cacheResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_657_ = stack[0].m_obj;
lean_object* v_r_658_ = stack[1].m_obj;
lean_object* v_a_659_ = stack[2].m_obj;
lean_object* v_a_660_ = stack[3].m_obj;
lean_object* v_a_661_ = stack[4].m_obj;
lean_object* v_a_662_ = stack[5].m_obj;
lean_object* v_a_663_ = stack[6].m_obj;
lean_object* v_a_664_ = stack[7].m_obj;
lean_object* v_a_665_ = stack[8].m_obj;
lean_object* v_a_666_ = stack[9].m_obj;
lean_object* v_a_667_ = stack[10].m_obj;
lean_object* v_res_705_;
v_res_705_ = l_Lean_Meta_Sym_Simp_cacheResult(v_e_657_, v_r_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object* v_e_706_, lean_object* v_r_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_Sym_Simp_cacheResult(v_e_706_, v_r_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
return v_res_718_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(lean_object* v_a_719_, lean_object* v_persistentCache_720_, lean_object* v_transientCache_721_, lean_object* v_funext_722_, lean_object* v_a_x3f_723_){
_start:
{
lean_object* v___x_725_; lean_object* v_numSteps_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_736_; 
v___x_725_ = lean_st_ref_take(v_a_719_);
v_numSteps_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; 
v_unused_737_ = lean_ctor_get(v___x_725_, 3);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v___x_725_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v___x_725_, 1);
lean_dec(v_unused_739_);
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_numSteps_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v_funext_722_);
lean_ctor_set(v___x_728_, 2, v_transientCache_721_);
lean_ctor_set(v___x_728_, 1, v_persistentCache_720_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_numSteps_726_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_persistentCache_720_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_transientCache_721_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_funext_722_);
v___x_732_ = v_reuseFailAlloc_735_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_st_ref_put(v_a_719_, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_730_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_719_ = stack[0].m_obj;
lean_object* v_persistentCache_720_ = stack[1].m_obj;
lean_object* v_transientCache_721_ = stack[2].m_obj;
lean_object* v_funext_722_ = stack[3].m_obj;
lean_object* v_a_x3f_723_ = stack[4].m_obj;
lean_object* v_res_740_;
v_res_740_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_719_, v_persistentCache_720_, v_transientCache_721_, v_funext_722_, v_a_x3f_723_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(lean_object* v_a_741_, lean_object* v_persistentCache_742_, lean_object* v_transientCache_743_, lean_object* v_funext_744_, lean_object* v_a_x3f_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_741_, v_persistentCache_742_, v_transientCache_743_, v_funext_744_, v_a_x3f_745_);
lean_dec(v_a_x3f_745_);
lean_dec(v_a_741_);
return v_res_747_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(lean_object* v_k_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_persistentCache_760_; lean_object* v___x_761_; lean_object* v_transientCache_762_; lean_object* v___x_763_; lean_object* v_funext_764_; lean_object* v_r_765_; 
v___x_759_ = lean_st_ref_get(v_a_751_);
v_persistentCache_760_ = lean_ctor_get(v___x_759_, 1);
lean_inc_ref(v_persistentCache_760_);
lean_dec(v___x_759_);
v___x_761_ = lean_st_ref_get(v_a_751_);
v_transientCache_762_ = lean_ctor_get(v___x_761_, 2);
lean_inc_ref(v_transientCache_762_);
lean_dec(v___x_761_);
v___x_763_ = lean_st_ref_get(v_a_751_);
v_funext_764_ = lean_ctor_get(v___x_763_, 3);
lean_inc_ref(v_funext_764_);
lean_dec(v___x_763_);
lean_inc(v_a_757_);
lean_inc_ref(v_a_756_);
lean_inc(v_a_755_);
lean_inc_ref(v_a_754_);
lean_inc(v_a_753_);
lean_inc_ref(v_a_752_);
lean_inc(v_a_751_);
lean_inc_ref(v_a_750_);
lean_inc(v_a_749_);
v_r_765_ = lean_apply_10(v_k_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, lean_box(0));
if (lean_obj_tag(v_r_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_782_; 
v_a_766_ = lean_ctor_get(v_r_765_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_r_765_);
if (v_isSharedCheck_782_ == 0)
{
v___x_768_ = v_r_765_;
v_isShared_769_ = v_isSharedCheck_782_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v_r_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_782_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
lean_inc(v_a_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_781_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v___x_772_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_751_, v_persistentCache_760_, v_transientCache_762_, v_funext_764_, v___x_771_);
lean_dec_ref(v___x_771_);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_772_, 0);
lean_dec(v_unused_780_);
v___x_774_ = v___x_772_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_dec(v___x_772_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_a_766_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_766_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_783_ = lean_ctor_get(v_r_765_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v_r_765_, 1);
v___x_784_ = lean_box(0);
v___x_785_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_751_, v_persistentCache_760_, v_transientCache_762_, v_funext_764_, v___x_784_);
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
lean_ctor_set_tag(v___x_787_, 1);
lean_ctor_set(v___x_787_, 0, v_a_783_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_783_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_748_ = stack[0].m_obj;
lean_object* v_a_749_ = stack[1].m_obj;
lean_object* v_a_750_ = stack[2].m_obj;
lean_object* v_a_751_ = stack[3].m_obj;
lean_object* v_a_752_ = stack[4].m_obj;
lean_object* v_a_753_ = stack[5].m_obj;
lean_object* v_a_754_ = stack[6].m_obj;
lean_object* v_a_755_ = stack[7].m_obj;
lean_object* v_a_756_ = stack[8].m_obj;
lean_object* v_a_757_ = stack[9].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(lean_object* v_k_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(v_k_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
return v_res_806_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_object* v_00_u03b1_807_, lean_object* v_k_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_persistentCache_820_; lean_object* v___x_821_; lean_object* v_transientCache_822_; lean_object* v___x_823_; lean_object* v_funext_824_; lean_object* v_r_825_; 
v___x_819_ = lean_st_ref_get(v_a_811_);
v_persistentCache_820_ = lean_ctor_get(v___x_819_, 1);
lean_inc_ref(v_persistentCache_820_);
lean_dec(v___x_819_);
v___x_821_ = lean_st_ref_get(v_a_811_);
v_transientCache_822_ = lean_ctor_get(v___x_821_, 2);
lean_inc_ref(v_transientCache_822_);
lean_dec(v___x_821_);
v___x_823_ = lean_st_ref_get(v_a_811_);
v_funext_824_ = lean_ctor_get(v___x_823_, 3);
lean_inc_ref(v_funext_824_);
lean_dec(v___x_823_);
lean_inc(v_a_817_);
lean_inc_ref(v_a_816_);
lean_inc(v_a_815_);
lean_inc_ref(v_a_814_);
lean_inc(v_a_813_);
lean_inc_ref(v_a_812_);
lean_inc(v_a_811_);
lean_inc_ref(v_a_810_);
lean_inc(v_a_809_);
v_r_825_ = lean_apply_10(v_k_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, lean_box(0));
if (lean_obj_tag(v_r_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_842_; 
v_a_826_ = lean_ctor_get(v_r_825_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_r_825_);
if (v_isSharedCheck_842_ == 0)
{
v___x_828_ = v_r_825_;
v_isShared_829_ = v_isSharedCheck_842_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v_r_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_842_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
lean_inc(v_a_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 1);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_841_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v___x_832_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_811_, v_persistentCache_820_, v_transientCache_822_, v_funext_824_, v___x_831_);
lean_dec_ref(v___x_831_);
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
lean_ctor_set(v___x_834_, 0, v_a_826_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_826_);
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
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_843_ = lean_ctor_get(v_r_825_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v_r_825_, 1);
v___x_844_ = lean_box(0);
v___x_845_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(v_a_811_, v_persistentCache_820_, v_transientCache_822_, v_funext_824_, v___x_844_);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_853_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 0, v_a_843_);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_843_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_withoutModifyingCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_808_ = stack[1].m_obj;
lean_object* v_a_809_ = stack[2].m_obj;
lean_object* v_a_810_ = stack[3].m_obj;
lean_object* v_a_811_ = stack[4].m_obj;
lean_object* v_a_812_ = stack[5].m_obj;
lean_object* v_a_813_ = stack[6].m_obj;
lean_object* v_a_814_ = stack[7].m_obj;
lean_object* v_a_815_ = stack[8].m_obj;
lean_object* v_a_816_ = stack[9].m_obj;
lean_object* v_a_817_ = stack[10].m_obj;
lean_object* v_res_854_;
v_res_854_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(lean_box(0), v_k_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(lean_object* v_00_u03b1_855_, lean_object* v_k_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(v_00_u03b1_855_, v_k_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
return v_res_867_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(lean_object* v_a_868_, lean_object* v_transientCache_869_, lean_object* v_funext_870_, lean_object* v_a_x3f_871_){
_start:
{
lean_object* v___x_873_; lean_object* v_numSteps_874_; lean_object* v_persistentCache_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_885_; 
v___x_873_ = lean_st_ref_take(v_a_868_);
v_numSteps_874_ = lean_ctor_get(v___x_873_, 0);
v_persistentCache_875_ = lean_ctor_get(v___x_873_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_886_ = lean_ctor_get(v___x_873_, 3);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v___x_873_, 2);
lean_dec(v_unused_887_);
v___x_877_ = v___x_873_;
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_persistentCache_875_);
lean_inc(v_numSteps_874_);
lean_dec(v___x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 3, v_funext_870_);
lean_ctor_set(v___x_877_, 2, v_transientCache_869_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_numSteps_874_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_persistentCache_875_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_transientCache_869_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_funext_870_);
v___x_881_ = v_reuseFailAlloc_884_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_st_ref_put(v_a_868_, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_879_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_868_ = stack[0].m_obj;
lean_object* v_transientCache_869_ = stack[1].m_obj;
lean_object* v_funext_870_ = stack[2].m_obj;
lean_object* v_a_x3f_871_ = stack[3].m_obj;
lean_object* v_res_888_;
v_res_888_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_868_, v_transientCache_869_, v_funext_870_, v_a_x3f_871_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(lean_object* v_a_889_, lean_object* v_transientCache_890_, lean_object* v_funext_891_, lean_object* v_a_x3f_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_889_, v_transientCache_890_, v_funext_891_, v_a_x3f_892_);
lean_dec(v_a_x3f_892_);
lean_dec(v_a_889_);
return v_res_894_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(lean_object* v_k_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v_transientCache_907_; lean_object* v___x_908_; lean_object* v_funext_909_; lean_object* v_r_910_; 
v___x_906_ = lean_st_ref_get(v_a_898_);
v_transientCache_907_ = lean_ctor_get(v___x_906_, 2);
lean_inc_ref(v_transientCache_907_);
lean_dec(v___x_906_);
v___x_908_ = lean_st_ref_get(v_a_898_);
v_funext_909_ = lean_ctor_get(v___x_908_, 3);
lean_inc_ref(v_funext_909_);
lean_dec(v___x_908_);
lean_inc(v_a_904_);
lean_inc_ref(v_a_903_);
lean_inc(v_a_902_);
lean_inc_ref(v_a_901_);
lean_inc(v_a_900_);
lean_inc_ref(v_a_899_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
v_r_910_ = lean_apply_10(v_k_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, lean_box(0));
if (lean_obj_tag(v_r_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_927_; 
v_a_911_ = lean_ctor_get(v_r_910_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v_r_910_);
if (v_isSharedCheck_927_ == 0)
{
v___x_913_ = v_r_910_;
v_isShared_914_ = v_isSharedCheck_927_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v_r_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_927_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
lean_inc(v_a_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 1);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_926_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v___x_917_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_898_, v_transientCache_907_, v_funext_909_, v___x_916_);
lean_dec_ref(v___x_916_);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_917_, 0);
lean_dec(v_unused_925_);
v___x_919_ = v___x_917_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_dec(v___x_917_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_a_911_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_911_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_a_928_ = lean_ctor_get(v_r_910_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v_r_910_, 1);
v___x_929_ = lean_box(0);
v___x_930_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_898_, v_transientCache_907_, v_funext_909_, v___x_929_);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_938_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 1);
lean_ctor_set(v___x_932_, 0, v_a_928_);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_928_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_895_ = stack[0].m_obj;
lean_object* v_a_896_ = stack[1].m_obj;
lean_object* v_a_897_ = stack[2].m_obj;
lean_object* v_a_898_ = stack[3].m_obj;
lean_object* v_a_899_ = stack[4].m_obj;
lean_object* v_a_900_ = stack[5].m_obj;
lean_object* v_a_901_ = stack[6].m_obj;
lean_object* v_a_902_ = stack[7].m_obj;
lean_object* v_a_903_ = stack[8].m_obj;
lean_object* v_a_904_ = stack[9].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(v_k_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(lean_object* v_k_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(v_k_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
return v_res_951_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_object* v_00_u03b1_952_, lean_object* v_k_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; lean_object* v_transientCache_965_; lean_object* v___x_966_; lean_object* v_funext_967_; lean_object* v_r_968_; 
v___x_964_ = lean_st_ref_get(v_a_956_);
v_transientCache_965_ = lean_ctor_get(v___x_964_, 2);
lean_inc_ref(v_transientCache_965_);
lean_dec(v___x_964_);
v___x_966_ = lean_st_ref_get(v_a_956_);
v_funext_967_ = lean_ctor_get(v___x_966_, 3);
lean_inc_ref(v_funext_967_);
lean_dec(v___x_966_);
lean_inc(v_a_962_);
lean_inc_ref(v_a_961_);
lean_inc(v_a_960_);
lean_inc_ref(v_a_959_);
lean_inc(v_a_958_);
lean_inc_ref(v_a_957_);
lean_inc(v_a_956_);
lean_inc_ref(v_a_955_);
lean_inc(v_a_954_);
v_r_968_ = lean_apply_10(v_k_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, lean_box(0));
if (lean_obj_tag(v_r_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_985_; 
v_a_969_ = lean_ctor_get(v_r_968_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_r_968_);
if (v_isSharedCheck_985_ == 0)
{
v___x_971_ = v_r_968_;
v_isShared_972_ = v_isSharedCheck_985_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v_r_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_985_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
lean_inc(v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_984_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v___x_975_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_956_, v_transientCache_965_, v_funext_967_, v___x_974_);
lean_dec_ref(v___x_974_);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_983_);
v___x_977_ = v___x_975_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_975_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_a_969_);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_969_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_986_ = lean_ctor_get(v_r_968_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v_r_968_, 1);
v___x_987_ = lean_box(0);
v___x_988_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(v_a_956_, v_transientCache_965_, v_funext_967_, v___x_987_);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_988_, 0);
lean_dec(v_unused_996_);
v___x_990_ = v___x_988_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_dec(v___x_988_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 0, v_a_986_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_986_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_withFreshTransientCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_953_ = stack[1].m_obj;
lean_object* v_a_954_ = stack[2].m_obj;
lean_object* v_a_955_ = stack[3].m_obj;
lean_object* v_a_956_ = stack[4].m_obj;
lean_object* v_a_957_ = stack[5].m_obj;
lean_object* v_a_958_ = stack[6].m_obj;
lean_object* v_a_959_ = stack[7].m_obj;
lean_object* v_a_960_ = stack[8].m_obj;
lean_object* v_a_961_ = stack[9].m_obj;
lean_object* v_a_962_ = stack[10].m_obj;
lean_object* v_res_997_;
v_res_997_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(lean_box(0), v_k_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(lean_object* v_00_u03b1_998_, lean_object* v_k_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(v_00_u03b1_998_, v_k_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
return v_res_1010_;
}
}
lean_object* l_Lean_Meta_Sym_simp(lean_object* v_e_1011_, lean_object* v_methods_1012_, lean_object* v_config_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1021_, 0, v_e_1011_);
v___x_1022_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1021_, v_methods_1012_, v_config_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1022_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1011_ = stack[0].m_obj;
lean_object* v_methods_1012_ = stack[1].m_obj;
lean_object* v_config_1013_ = stack[2].m_obj;
lean_object* v_a_1014_ = stack[3].m_obj;
lean_object* v_a_1015_ = stack[4].m_obj;
lean_object* v_a_1016_ = stack[5].m_obj;
lean_object* v_a_1017_ = stack[6].m_obj;
lean_object* v_a_1018_ = stack[7].m_obj;
lean_object* v_a_1019_ = stack[8].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Lean_Meta_Sym_simp(v_e_1011_, v_methods_1012_, v_config_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simp___boxed(lean_object* v_e_1024_, lean_object* v_methods_1025_, lean_object* v_config_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_Sym_simp(v_e_1024_, v_methods_1025_, v_config_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1034_;
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
