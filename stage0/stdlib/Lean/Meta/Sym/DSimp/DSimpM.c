// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.DSimpM
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ExprPtr
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
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_rfl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_rfl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedResult_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedResult = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42;
static const lean_string_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<default>"};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value),((lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(100000u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(100000u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(0u);
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(1u);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Meta_Sym_DSimp_Result_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 0)
{
uint8_t v_done_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_done_10_ = lean_ctor_get_uint8(v_t_8_, 0);
lean_dec_ref_known(v_t_8_, 0);
v___x_11_ = lean_box(v_done_10_);
v___x_12_ = lean_apply_1(v_k_9_, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_e_x27_13_; uint8_t v_done_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_e_x27_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_e_x27_13_);
v_done_14_ = lean_ctor_get_uint8(v_t_8_, sizeof(void*)*1);
lean_dec_ref_known(v_t_8_, 1);
v___x_15_ = lean_box(v_done_14_);
v___x_16_ = lean_apply_2(v_k_9_, v_e_x27_13_, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_rfl_elim___redArg(lean_object* v_t_29_, lean_object* v_rfl_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_29_, v_rfl_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_rfl_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_rfl_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_33_, v_rfl_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_step_elim___redArg(lean_object* v_t_37_, lean_object* v_step_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_37_, v_step_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_step_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_step_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_41_, v_step_43_);
return v___x_44_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_instMonadEIO(lean_box(0));
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0);
v___x_52_ = l_StateRefT_x27_instMonad___redArg(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6(void){
_start:
{
lean_object* v___x_57_; lean_object* v___f_58_; 
v___x_57_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_58_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_58_, 0, v___x_57_);
return v___f_58_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7(void){
_start:
{
lean_object* v___x_59_; lean_object* v___f_60_; 
v___x_59_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_60_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_60_, 0, v___x_59_);
return v___f_60_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8(void){
_start:
{
lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v___f_61_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7);
v___f_62_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___f_62_);
lean_ctor_set(v___x_63_, 1, v___f_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9(void){
_start:
{
lean_object* v___x_64_; lean_object* v___f_65_; 
v___x_64_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8);
v___f_65_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_65_, 0, v___x_64_);
return v___f_65_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10(void){
_start:
{
lean_object* v___x_66_; lean_object* v___f_67_; 
v___x_66_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8);
v___f_67_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_67_, 0, v___x_66_);
return v___f_67_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11(void){
_start:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
v___f_68_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10);
v___f_69_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___f_69_);
lean_ctor_set(v___x_70_, 1, v___f_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12(void){
_start:
{
lean_object* v___x_71_; lean_object* v___f_72_; 
v___x_71_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11);
v___f_72_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_72_, 0, v___x_71_);
return v___f_72_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13(void){
_start:
{
lean_object* v___x_73_; lean_object* v___f_74_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11);
v___f_74_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_74_, 0, v___x_73_);
return v___f_74_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14(void){
_start:
{
lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_77_; 
v___f_75_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13);
v___f_76_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___f_76_);
lean_ctor_set(v___x_77_, 1, v___f_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15(void){
_start:
{
lean_object* v___x_78_; lean_object* v___f_79_; 
v___x_78_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14);
v___f_79_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_79_, 0, v___x_78_);
return v___f_79_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16(void){
_start:
{
lean_object* v___x_80_; lean_object* v___f_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_81_, 0, v___x_80_);
return v___f_81_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17(void){
_start:
{
lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; 
v___f_82_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16);
v___f_83_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___f_83_);
lean_ctor_set(v___x_84_, 1, v___f_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18(void){
_start:
{
lean_object* v___x_85_; lean_object* v___f_86_; 
v___x_85_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17);
v___f_86_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_86_, 0, v___x_85_);
return v___f_86_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19(void){
_start:
{
lean_object* v___x_87_; lean_object* v___f_88_; 
v___x_87_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17);
v___f_88_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_88_, 0, v___x_87_);
return v___f_88_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20(void){
_start:
{
lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
v___f_89_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19);
v___f_90_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___f_90_);
lean_ctor_set(v___x_91_, 1, v___f_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21(void){
_start:
{
lean_object* v___x_92_; lean_object* v___f_93_; 
v___x_92_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_93_, 0, v___x_92_);
return v___f_93_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22(void){
_start:
{
lean_object* v___x_94_; lean_object* v___f_95_; 
v___x_94_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_95_, 0, v___x_94_);
return v___f_95_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23(void){
_start:
{
lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___x_98_; 
v___f_96_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22);
v___f_97_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___f_97_);
lean_ctor_set(v___x_98_, 1, v___f_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24(void){
_start:
{
lean_object* v___x_99_; lean_object* v___f_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_100_, 0, v___x_99_);
return v___f_100_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25(void){
_start:
{
lean_object* v___x_101_; lean_object* v___f_102_; 
v___x_101_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23);
v___f_102_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_102_, 0, v___x_101_);
return v___f_102_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26(void){
_start:
{
lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; 
v___f_103_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25);
v___f_104_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___f_104_);
lean_ctor_set(v___x_105_, 1, v___f_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_111_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30));
v___x_112_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29));
v___x_113_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_112_, v___x_111_, v___x_110_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32(void){
_start:
{
lean_object* v___x_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31);
v___f_115_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_116_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27));
v___x_117_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_116_, v___f_115_, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32);
v___x_119_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30));
v___x_120_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29));
v___x_121_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_120_, v___x_119_, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34(void){
_start:
{
lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33);
v___f_123_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_124_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27));
v___x_125_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_124_, v___f_123_, v___x_122_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30));
v___x_128_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29));
v___x_129_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_128_, v___x_127_, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36(void){
_start:
{
lean_object* v___x_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35);
v___f_131_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_132_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27));
v___x_133_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_132_, v___f_131_, v___x_130_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37(void){
_start:
{
lean_object* v___x_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___x_137_; 
v___x_134_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36);
v___f_135_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_136_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27));
v___x_137_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_136_, v___f_135_, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___f_140_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30));
v___x_139_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_140_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_140_, 0, v___x_139_);
lean_closure_set(v___f_140_, 1, v___x_138_);
return v___f_140_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39(void){
_start:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; 
v___f_141_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_142_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_143_, 0, v___f_142_);
lean_closure_set(v___f_143_, 1, v___f_141_);
return v___f_143_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40(void){
_start:
{
lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___f_146_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30));
v___f_145_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_146_, 0, v___f_145_);
lean_closure_set(v___f_146_, 1, v___x_144_);
return v___f_146_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41(void){
_start:
{
lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; 
v___f_147_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_148_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_149_, 0, v___f_148_);
lean_closure_set(v___f_149_, 1, v___f_147_);
return v___f_149_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42(void){
_start:
{
lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___f_152_; 
v___f_150_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28));
v___f_151_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41);
v___f_152_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_152_, 0, v___f_151_);
lean_closure_set(v___f_152_, 1, v___f_150_);
return v___f_152_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43));
v___x_155_ = l_Lean_stringToMessageData(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(lean_object* v_00_u03b1_156_){
_start:
{
lean_object* v___x_157_; lean_object* v_toApplicative_158_; lean_object* v_toFunctor_159_; lean_object* v_toSeq_160_; lean_object* v_toSeqLeft_161_; lean_object* v_toSeqRight_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_toApplicative_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_214_; 
v___x_157_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1);
v_toApplicative_158_ = lean_ctor_get(v___x_157_, 0);
v_toFunctor_159_ = lean_ctor_get(v_toApplicative_158_, 0);
v_toSeq_160_ = lean_ctor_get(v_toApplicative_158_, 2);
v_toSeqLeft_161_ = lean_ctor_get(v_toApplicative_158_, 3);
v_toSeqRight_162_ = lean_ctor_get(v_toApplicative_158_, 4);
v___f_163_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2));
v___f_164_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3));
lean_inc_ref_n(v_toFunctor_159_, 2);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_165_, 0, v_toFunctor_159_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_166_, 0, v_toFunctor_159_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___f_165_);
lean_ctor_set(v___x_167_, 1, v___f_166_);
lean_inc(v_toSeqRight_162_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeqRight_162_);
lean_inc(v_toSeqLeft_161_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_169_, 0, v_toSeqLeft_161_);
lean_inc(v_toSeq_160_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_170_, 0, v_toSeq_160_);
v___x_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_171_, 0, v___x_167_);
lean_ctor_set(v___x_171_, 1, v___f_163_);
lean_ctor_set(v___x_171_, 2, v___f_170_);
lean_ctor_set(v___x_171_, 3, v___f_169_);
lean_ctor_set(v___x_171_, 4, v___f_168_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___f_164_);
v___x_173_ = l_StateRefT_x27_instMonad___redArg(v___x_172_);
v_toApplicative_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v___x_173_, 1);
lean_dec(v_unused_215_);
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_214_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_toApplicative_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_214_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_toFunctor_178_; lean_object* v_toSeq_179_; lean_object* v_toSeqLeft_180_; lean_object* v_toSeqRight_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_212_; 
v_toFunctor_178_ = lean_ctor_get(v_toApplicative_174_, 0);
v_toSeq_179_ = lean_ctor_get(v_toApplicative_174_, 2);
v_toSeqLeft_180_ = lean_ctor_get(v_toApplicative_174_, 3);
v_toSeqRight_181_ = lean_ctor_get(v_toApplicative_174_, 4);
v_isSharedCheck_212_ = !lean_is_exclusive(v_toApplicative_174_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_dec(v_unused_213_);
v___x_183_ = v_toApplicative_174_;
v_isShared_184_ = v_isSharedCheck_212_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_toSeqRight_181_);
lean_inc(v_toSeqLeft_180_);
lean_inc(v_toSeq_179_);
lean_inc(v_toFunctor_178_);
lean_dec(v_toApplicative_174_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_212_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_194_; 
v___f_185_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4));
v___f_186_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5));
lean_inc_ref(v_toFunctor_178_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_187_, 0, v_toFunctor_178_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_188_, 0, v_toFunctor_178_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___f_187_);
lean_ctor_set(v___x_189_, 1, v___f_188_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeqRight_181_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_191_, 0, v_toSeqLeft_180_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_192_, 0, v_toSeq_179_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___f_190_);
lean_ctor_set(v___x_183_, 3, v___f_191_);
lean_ctor_set(v___x_183_, 2, v___f_192_);
lean_ctor_set(v___x_183_, 1, v___f_185_);
lean_ctor_set(v___x_183_, 0, v___x_189_);
v___x_194_ = v___x_183_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___f_185_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v___f_190_);
v___x_194_ = v_reuseFailAlloc_211_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___f_186_);
lean_ctor_set(v___x_176_, 0, v___x_194_);
v___x_196_ = v___x_176_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___f_186_);
v___x_196_ = v_reuseFailAlloc_210_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_toMonadRef_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_197_ = l_StateRefT_x27_instMonad___redArg(v___x_196_);
v___x_198_ = l_ReaderT_instMonad___redArg(v___x_197_);
v___x_199_ = l_StateRefT_x27_instMonad___redArg(v___x_198_);
v___x_200_ = l_ReaderT_instMonad___redArg(v___x_199_);
v___x_201_ = l_ReaderT_instMonad___redArg(v___x_200_);
v___x_202_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26);
v___x_203_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37);
v_toMonadRef_204_ = lean_ctor_get(v___x_203_, 0);
v___f_205_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42);
lean_inc_ref(v___x_201_);
v___x_206_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_205_, v___x_201_);
lean_inc_ref(v_toMonadRef_204_);
v___x_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_207_, 0, v___x_202_);
lean_ctor_set(v___x_207_, 1, v_toMonadRef_204_);
lean_ctor_set(v___x_207_, 2, v___x_206_);
v___x_208_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44);
v___x_209_ = l_Lean_throwError___redArg(v___x_201_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(lean_object* v_x_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0));
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(v_x_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v_x_229_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(lean_object* v_m_246_){
_start:
{
lean_inc_ref(v_m_246_);
return v_m_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(v_m_247_);
lean_dec_ref(v_m_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(lean_object* v_m_249_){
_start:
{
lean_inc(v_m_249_);
return v_m_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(v_m_250_);
lean_dec(v_m_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg(lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; 
lean_inc(v_a_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_a_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg___boxed(lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Sym_DSimp_getMethods___redArg(v_a_255_);
lean_dec(v_a_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods(lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; 
lean_inc(v_a_258_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_a_258_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___boxed(lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Sym_DSimp_getMethods(v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec(v_a_270_);
lean_dec(v_a_269_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object* v_x_280_, lean_object* v_methods_281_, lean_object* v_config_282_, lean_object* v_s_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_cache_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_319_; 
v_cache_291_ = lean_ctor_get(v_s_283_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_s_283_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_s_283_, 0);
lean_dec(v_unused_320_);
v___x_293_ = v_s_283_;
v_isShared_294_ = v_isSharedCheck_319_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_cache_291_);
lean_dec(v_s_283_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_319_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_unsigned_to_nat(0u);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_cache_291_);
v___x_297_ = v_reuseFailAlloc_318_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_st_mk_ref(v___x_297_);
lean_inc(v_a_289_);
lean_inc_ref(v_a_288_);
lean_inc(v_a_287_);
lean_inc_ref(v_a_286_);
lean_inc(v_a_285_);
lean_inc_ref(v_a_284_);
lean_inc(v___x_298_);
v___x_299_ = lean_apply_10(v_x_280_, v_methods_281_, v_config_282_, v___x_298_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, lean_box(0));
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_309_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_309_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_st_ref_get(v___x_298_);
lean_dec(v___x_298_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_a_300_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v___x_298_);
v_a_310_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_299_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_299_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___boxed(lean_object* v_x_321_, lean_object* v_methods_322_, lean_object* v_config_323_, lean_object* v_s_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v_x_321_, v_methods_322_, v_config_323_, v_s_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run(lean_object* v_00_u03b1_333_, lean_object* v_x_334_, lean_object* v_methods_335_, lean_object* v_config_336_, lean_object* v_s_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v_x_334_, v_methods_335_, v_config_336_, v_s_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___boxed(lean_object* v_00_u03b1_346_, lean_object* v_x_347_, lean_object* v_methods_348_, lean_object* v_config_349_, lean_object* v_s_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Sym_DSimp_DSimpM_run(v_00_u03b1_346_, v_x_347_, v_methods_348_, v_config_349_, v_s_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_358_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(lean_object* v_x_365_, lean_object* v_methods_366_, lean_object* v_config_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2);
v___x_376_ = lean_st_mk_ref(v___x_375_);
lean_inc(v_a_373_);
lean_inc_ref(v_a_372_);
lean_inc(v_a_371_);
lean_inc_ref(v_a_370_);
lean_inc(v_a_369_);
lean_inc_ref(v_a_368_);
lean_inc(v___x_376_);
v___x_377_ = lean_apply_10(v_x_365_, v_methods_366_, v_config_367_, v___x_376_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, lean_box(0));
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_st_ref_get(v___x_376_);
lean_dec(v___x_376_);
lean_dec(v___x_382_);
if (v_isShared_381_ == 0)
{
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_378_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_dec(v___x_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___boxed(lean_object* v_x_387_, lean_object* v_methods_388_, lean_object* v_config_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_387_, v_methods_388_, v_config_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(lean_object* v_00_u03b1_398_, lean_object* v_x_399_, lean_object* v_methods_400_, lean_object* v_config_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_399_, v_methods_400_, v_config_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___boxed(lean_object* v_00_u03b1_410_, lean_object* v_x_411_, lean_object* v_methods_412_, lean_object* v_config_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(v_00_u03b1_410_, v_x_411_, v_methods_412_, v_config_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object* v_a_00___x40___internal___hyg_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_00___x40___internal___hyg_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = lean_sym_dsimp(v_a_00___x40___internal___hyg_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg(lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; 
lean_inc(v_a_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_a_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg___boxed(lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Sym_DSimp_getConfig___redArg(v_a_448_);
lean_dec(v_a_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig(lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; 
lean_inc(v_a_452_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_a_452_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___boxed(lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Sym_DSimp_getConfig(v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
lean_dec(v_a_462_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_pre_484_; lean_object* v___x_485_; 
v_pre_484_ = lean_ctor_get(v_a_474_, 0);
lean_inc_ref(v_pre_484_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc_ref(v_a_479_);
lean_inc(v_a_478_);
lean_inc_ref(v_a_477_);
lean_inc(v_a_476_);
lean_inc(v_a_475_);
lean_inc(v_a_474_);
v___x_485_ = lean_apply_11(v_pre_484_, v_e_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, lean_box(0));
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre___boxed(lean_object* v_e_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Meta_Sym_DSimp_pre(v_e_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec(v_a_488_);
lean_dec(v_a_487_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post(lean_object* v_e_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_post_509_; lean_object* v___x_510_; 
v_post_509_ = lean_ctor_get(v_a_499_, 1);
lean_inc_ref(v_post_509_);
lean_inc(v_a_507_);
lean_inc_ref(v_a_506_);
lean_inc(v_a_505_);
lean_inc_ref(v_a_504_);
lean_inc(v_a_503_);
lean_inc_ref(v_a_502_);
lean_inc(v_a_501_);
lean_inc(v_a_500_);
lean_inc(v_a_499_);
v___x_510_ = lean_apply_11(v_post_509_, v_e_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, lean_box(0));
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post___boxed(lean_object* v_e_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Sym_DSimp_post(v_e_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
lean_dec(v_a_512_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp(lean_object* v_e_523_, lean_object* v_methods_524_, lean_object* v_config_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_inc_ref(v_e_523_);
v___x_533_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_533_, 0, v_e_523_);
v___x_534_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v___x_533_, v_methods_524_, v_config_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_546_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_546_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
if (lean_obj_tag(v_a_535_) == 0)
{
lean_object* v___x_540_; 
lean_dec_ref_known(v_a_535_, 0);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_e_523_);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_e_523_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
else
{
lean_object* v_e_x27_542_; lean_object* v___x_544_; 
lean_dec_ref(v_e_523_);
v_e_x27_542_ = lean_ctor_get(v_a_535_, 0);
lean_inc_ref(v_e_x27_542_);
lean_dec_ref_known(v_a_535_, 1);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_e_x27_542_);
v___x_544_ = v___x_537_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_e_x27_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_e_523_);
v_a_547_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_534_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_534_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp___boxed(lean_object* v_e_555_, lean_object* v_methods_556_, lean_object* v_config_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_Sym_dsimp(v_e_555_, v_methods_556_, v_config_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
return v_res_565_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default = _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default();
lean_mark_persistent(l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default);
l_Lean_Meta_Sym_DSimp_instInhabitedConfig = _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Meta_Sym_DSimp_instInhabitedConfig);
l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed = _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
}
#ifdef __cplusplus
}
#endif
