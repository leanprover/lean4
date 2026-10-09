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
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx___impl___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__12;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__15;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__21;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__25;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__26;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__29_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__31;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__32;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__33;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__34;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__35;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__36;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__37;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__38;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__39;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__40;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__41;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__42;
static const lean_string_object l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<default>"};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__43 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__44;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx___impl(lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorIdx___impl___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Sym_DSimp_Result_ctorIdx___impl(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
if (lean_obj_tag(v_t_10_) == 0)
{
uint8_t v_done_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_done_12_ = lean_ctor_get_uint8(v_t_10_, 0);
lean_dec_ref_known(v_t_10_, 0);
v___x_13_ = lean_box(v_done_12_);
v___x_14_ = lean_apply_1(v_k_11_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_e_x27_15_; uint8_t v_done_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_e_x27_15_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_e_x27_15_);
v_done_16_ = lean_ctor_get_uint8(v_t_10_, sizeof(void*)*1);
lean_dec_ref_known(v_t_10_, 1);
v___x_17_ = lean_box(v_done_16_);
v___x_18_ = lean_apply_2(v_k_11_, v_e_x27_15_, v___x_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_rfl_elim___redArg(lean_object* v_t_31_, lean_object* v_rfl_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_31_, v_rfl_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_rfl_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_rfl_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_35_, v_rfl_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_step_elim___redArg(lean_object* v_t_39_, lean_object* v_step_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_39_, v_step_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_step_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_step_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_43_, v_step_45_);
return v___x_46_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__0(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_instMonadEIO___redArg();
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__0, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__0);
v___x_54_ = l_StateRefT_x27_instMonad___redArg(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__6(void){
_start:
{
lean_object* v___x_59_; lean_object* v___f_60_; 
v___x_59_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_60_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_60_, 0, v___x_59_);
return v___f_60_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__7(void){
_start:
{
lean_object* v___x_61_; lean_object* v___f_62_; 
v___x_61_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_62_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_62_, 0, v___x_61_);
return v___f_62_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8(void){
_start:
{
lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v___f_63_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__7, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__7);
v___f_64_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__6, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__6);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___f_64_);
lean_ctor_set(v___x_65_, 1, v___f_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__9(void){
_start:
{
lean_object* v___x_66_; lean_object* v___f_67_; 
v___x_66_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8);
v___f_67_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_67_, 0, v___x_66_);
return v___f_67_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__10(void){
_start:
{
lean_object* v___x_68_; lean_object* v___f_69_; 
v___x_68_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__8);
v___f_69_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_69_, 0, v___x_68_);
return v___f_69_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11(void){
_start:
{
lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___x_72_; 
v___f_70_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__10, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__10);
v___f_71_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__9, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__9);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___f_71_);
lean_ctor_set(v___x_72_, 1, v___f_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__12(void){
_start:
{
lean_object* v___x_73_; lean_object* v___f_74_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11);
v___f_74_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_74_, 0, v___x_73_);
return v___f_74_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__13(void){
_start:
{
lean_object* v___x_75_; lean_object* v___f_76_; 
v___x_75_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__11);
v___f_76_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_76_, 0, v___x_75_);
return v___f_76_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14(void){
_start:
{
lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___x_79_; 
v___f_77_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__13, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__13_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__13);
v___f_78_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__12, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__12_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__12);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___f_78_);
lean_ctor_set(v___x_79_, 1, v___f_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__15(void){
_start:
{
lean_object* v___x_80_; lean_object* v___f_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_81_, 0, v___x_80_);
return v___f_81_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__16(void){
_start:
{
lean_object* v___x_82_; lean_object* v___f_83_; 
v___x_82_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__14);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_83_, 0, v___x_82_);
return v___f_83_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17(void){
_start:
{
lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_84_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__16, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__16);
v___f_85_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__15, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__15_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__15);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___f_85_);
lean_ctor_set(v___x_86_, 1, v___f_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__18(void){
_start:
{
lean_object* v___x_87_; lean_object* v___f_88_; 
v___x_87_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17);
v___f_88_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_88_, 0, v___x_87_);
return v___f_88_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__19(void){
_start:
{
lean_object* v___x_89_; lean_object* v___f_90_; 
v___x_89_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__17);
v___f_90_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_90_, 0, v___x_89_);
return v___f_90_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20(void){
_start:
{
lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; 
v___f_91_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__19, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__19);
v___f_92_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__18, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__18);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___f_92_);
lean_ctor_set(v___x_93_, 1, v___f_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__21(void){
_start:
{
lean_object* v___x_94_; lean_object* v___f_95_; 
v___x_94_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_95_, 0, v___x_94_);
return v___f_95_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__22(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; 
v___x_96_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__20);
v___f_97_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
return v___f_97_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23(void){
_start:
{
lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; 
v___f_98_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__22, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__22_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__22);
v___f_99_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__21, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__21);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___f_99_);
lean_ctor_set(v___x_100_, 1, v___f_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__24(void){
_start:
{
lean_object* v___x_101_; lean_object* v___f_102_; 
v___x_101_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23);
v___f_102_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_102_, 0, v___x_101_);
return v___f_102_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__25(void){
_start:
{
lean_object* v___x_103_; lean_object* v___f_104_; 
v___x_103_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__23);
v___f_104_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_104_, 0, v___x_103_);
return v___f_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__26(void){
_start:
{
lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v___f_105_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__25, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__25_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__25);
v___f_106_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__24, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__24_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__24);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___f_106_);
lean_ctor_set(v___x_107_, 1, v___f_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__31(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_113_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30));
v___x_114_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__29));
v___x_115_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_114_, v___x_113_, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__32(void){
_start:
{
lean_object* v___x_116_; lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__31, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__31_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__31);
v___f_117_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_118_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27));
v___x_119_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_118_, v___f_117_, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__33(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__32, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__32_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__32);
v___x_121_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30));
v___x_122_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__29));
v___x_123_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_122_, v___x_121_, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__34(void){
_start:
{
lean_object* v___x_124_; lean_object* v___f_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v___x_124_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__33, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__33_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__33);
v___f_125_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_126_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27));
v___x_127_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_126_, v___f_125_, v___x_124_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__35(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__34, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__34_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__34);
v___x_129_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30));
v___x_130_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__29));
v___x_131_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_130_, v___x_129_, v___x_128_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__36(void){
_start:
{
lean_object* v___x_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__35, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__35_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__35);
v___f_133_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_134_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27));
v___x_135_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_134_, v___f_133_, v___x_132_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__37(void){
_start:
{
lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__36, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__36_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__36);
v___f_137_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_138_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__27));
v___x_139_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_138_, v___f_137_, v___x_136_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__38(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___f_142_; 
v___x_140_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30));
v___x_141_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_142_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_142_, 0, v___x_141_);
lean_closure_set(v___f_142_, 1, v___x_140_);
return v___f_142_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__39(void){
_start:
{
lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; 
v___f_143_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_144_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__38, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__38_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__38);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_145_, 0, v___f_144_);
lean_closure_set(v___f_145_, 1, v___f_143_);
return v___f_145_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__40(void){
_start:
{
lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; 
v___x_146_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__30));
v___f_147_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__39, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__39_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__39);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_148_, 0, v___f_147_);
lean_closure_set(v___f_148_, 1, v___x_146_);
return v___f_148_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__41(void){
_start:
{
lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___f_151_; 
v___f_149_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_150_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__40, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__40_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__40);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_151_, 0, v___f_150_);
lean_closure_set(v___f_151_, 1, v___f_149_);
return v___f_151_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__42(void){
_start:
{
lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___f_154_; 
v___f_152_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__28));
v___f_153_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__41, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__41_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__41);
v___f_154_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_154_, 0, v___f_153_);
lean_closure_set(v___f_154_, 1, v___f_152_);
return v___f_154_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__44(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__43));
v___x_157_ = l_Lean_stringToMessageData(v___x_156_);
return v___x_157_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg(){
_start:
{
lean_object* v___x_159_; lean_object* v_toApplicative_160_; lean_object* v_toFunctor_161_; lean_object* v_toSeq_162_; lean_object* v_toSeqLeft_163_; lean_object* v_toSeqRight_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_toApplicative_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_216_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__1, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__1);
v_toApplicative_160_ = lean_ctor_get(v___x_159_, 0);
v_toFunctor_161_ = lean_ctor_get(v_toApplicative_160_, 0);
v_toSeq_162_ = lean_ctor_get(v_toApplicative_160_, 2);
v_toSeqLeft_163_ = lean_ctor_get(v_toApplicative_160_, 3);
v_toSeqRight_164_ = lean_ctor_get(v_toApplicative_160_, 4);
v___f_165_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__2));
v___f_166_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_161_, 2);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_167_, 0, v_toFunctor_161_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_168_, 0, v_toFunctor_161_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___f_167_);
lean_ctor_set(v___x_169_, 1, v___f_168_);
lean_inc(v_toSeqRight_164_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_170_, 0, v_toSeqRight_164_);
lean_inc(v_toSeqLeft_163_);
v___f_171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_171_, 0, v_toSeqLeft_163_);
lean_inc(v_toSeq_162_);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_172_, 0, v_toSeq_162_);
v___x_173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_173_, 0, v___x_169_);
lean_ctor_set(v___x_173_, 1, v___f_165_);
lean_ctor_set(v___x_173_, 2, v___f_172_);
lean_ctor_set(v___x_173_, 3, v___f_171_);
lean_ctor_set(v___x_173_, 4, v___f_170_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___f_166_);
v___x_175_ = l_StateRefT_x27_instMonad___redArg(v___x_174_);
v_toApplicative_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v___x_175_, 1);
lean_dec(v_unused_217_);
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_216_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toApplicative_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_216_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_toFunctor_180_; lean_object* v_toSeq_181_; lean_object* v_toSeqLeft_182_; lean_object* v_toSeqRight_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_214_; 
v_toFunctor_180_ = lean_ctor_get(v_toApplicative_176_, 0);
v_toSeq_181_ = lean_ctor_get(v_toApplicative_176_, 2);
v_toSeqLeft_182_ = lean_ctor_get(v_toApplicative_176_, 3);
v_toSeqRight_183_ = lean_ctor_get(v_toApplicative_176_, 4);
v_isSharedCheck_214_ = !lean_is_exclusive(v_toApplicative_176_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_dec(v_unused_215_);
v___x_185_ = v_toApplicative_176_;
v_isShared_186_ = v_isSharedCheck_214_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_toSeqRight_183_);
lean_inc(v_toSeqLeft_182_);
lean_inc(v_toSeq_181_);
lean_inc(v_toFunctor_180_);
lean_dec(v_toApplicative_176_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_214_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_196_; 
v___f_187_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__4));
v___f_188_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__5));
lean_inc_ref(v_toFunctor_180_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_189_, 0, v_toFunctor_180_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_190_, 0, v_toFunctor_180_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___f_189_);
lean_ctor_set(v___x_191_, 1, v___f_190_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_192_, 0, v_toSeqRight_183_);
v___f_193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_193_, 0, v_toSeqLeft_182_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_194_, 0, v_toSeq_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 4, v___f_192_);
lean_ctor_set(v___x_185_, 3, v___f_193_);
lean_ctor_set(v___x_185_, 2, v___f_194_);
lean_ctor_set(v___x_185_, 1, v___f_187_);
lean_ctor_set(v___x_185_, 0, v___x_191_);
v___x_196_ = v___x_185_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___f_187_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v___f_194_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v___f_193_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v___f_192_);
v___x_196_ = v_reuseFailAlloc_213_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___f_188_);
lean_ctor_set(v___x_178_, 0, v___x_196_);
v___x_198_ = v___x_178_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___f_188_);
v___x_198_ = v_reuseFailAlloc_212_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_toMonadRef_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_199_ = l_StateRefT_x27_instMonad___redArg(v___x_198_);
v___x_200_ = l_ReaderT_instMonad___redArg(v___x_199_);
v___x_201_ = l_StateRefT_x27_instMonad___redArg(v___x_200_);
v___x_202_ = l_ReaderT_instMonad___redArg(v___x_201_);
v___x_203_ = l_ReaderT_instMonad___redArg(v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__26, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__26_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__26);
v___x_205_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__37, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__37_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__37);
v_toMonadRef_206_ = lean_ctor_get(v___x_205_, 0);
v___f_207_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__42, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__42_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__42);
lean_inc_ref(v___x_203_);
v___x_208_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_207_, v___x_203_);
lean_inc_ref(v_toMonadRef_206_);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v___x_204_);
lean_ctor_set(v___x_209_, 1, v_toMonadRef_206_);
lean_ctor_set(v___x_209_, 2, v___x_208_);
v___x_210_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__44, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__44_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___closed__44);
v___x_211_ = l_Lean_throwError___redArg(v___x_203_, v___x_209_, v___x_210_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_218_;
v_res_218_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___boxed(lean_object* v___dummy_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
return v_res_220_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(lean_object* v_00_u03b1_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0);
return v___x_223_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0));
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_224_ = stack[0].m_obj;
lean_object* v___y_225_ = stack[1].m_obj;
lean_object* v___y_226_ = stack[2].m_obj;
lean_object* v___y_227_ = stack[3].m_obj;
lean_object* v___y_228_ = stack[4].m_obj;
lean_object* v___y_229_ = stack[5].m_obj;
lean_object* v___y_230_ = stack[6].m_obj;
lean_object* v___y_231_ = stack[7].m_obj;
lean_object* v___y_232_ = stack[8].m_obj;
lean_object* v___y_233_ = stack[9].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(v_x_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(v_x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v_x_238_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(lean_object* v_m_255_){
_start:
{
lean_inc_ref(v_m_255_);
return v_m_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(v_m_256_);
lean_dec_ref(v_m_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(lean_object* v_m_258_){
_start:
{
lean_inc(v_m_258_);
return v_m_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(v_m_259_);
lean_dec(v_m_259_);
return v_res_260_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg(lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc(v_a_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_a_261_);
return v___x_263_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_getMethods___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_261_ = stack[0].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lean_Meta_Sym_DSimp_getMethods___redArg(v_a_261_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg___boxed(lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_Sym_DSimp_getMethods___redArg(v_a_265_);
lean_dec(v_a_265_);
return v_res_267_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_getMethods(lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
lean_inc(v_a_268_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_a_268_);
return v___x_278_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_getMethods_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_268_ = stack[0].m_obj;
lean_object* v_a_269_ = stack[1].m_obj;
lean_object* v_a_270_ = stack[2].m_obj;
lean_object* v_a_271_ = stack[3].m_obj;
lean_object* v_a_272_ = stack[4].m_obj;
lean_object* v_a_273_ = stack[5].m_obj;
lean_object* v_a_274_ = stack[6].m_obj;
lean_object* v_a_275_ = stack[7].m_obj;
lean_object* v_a_276_ = stack[8].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_Meta_Sym_DSimp_getMethods(v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___boxed(lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Sym_DSimp_getMethods(v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
return v_res_290_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object* v_x_291_, lean_object* v_methods_292_, lean_object* v_config_293_, lean_object* v_s_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_cache_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_330_; 
v_cache_302_ = lean_ctor_get(v_s_294_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_s_294_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_s_294_, 0);
lean_dec(v_unused_331_);
v___x_304_ = v_s_294_;
v_isShared_305_ = v_isSharedCheck_330_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_cache_302_);
lean_dec(v_s_294_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_330_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_unsigned_to_nat(0u);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_cache_302_);
v___x_308_ = v_reuseFailAlloc_329_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_st_mk_ref(v___x_308_);
lean_inc(v_a_300_);
lean_inc_ref(v_a_299_);
lean_inc(v_a_298_);
lean_inc_ref(v_a_297_);
lean_inc(v_a_296_);
lean_inc_ref(v_a_295_);
lean_inc(v___x_309_);
v___x_310_ = lean_apply_10(v_x_291_, v_methods_292_, v_config_293_, v___x_309_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, lean_box(0));
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_320_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_320_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_320_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_320_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_315_ = lean_st_ref_get(v___x_309_);
lean_dec(v___x_309_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_311_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_316_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v___x_309_);
v_a_321_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_310_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_310_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_291_ = stack[0].m_obj;
lean_object* v_methods_292_ = stack[1].m_obj;
lean_object* v_config_293_ = stack[2].m_obj;
lean_object* v_s_294_ = stack[3].m_obj;
lean_object* v_a_295_ = stack[4].m_obj;
lean_object* v_a_296_ = stack[5].m_obj;
lean_object* v_a_297_ = stack[6].m_obj;
lean_object* v_a_298_ = stack[7].m_obj;
lean_object* v_a_299_ = stack[8].m_obj;
lean_object* v_a_300_ = stack[9].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v_x_291_, v_methods_292_, v_config_293_, v_s_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___boxed(lean_object* v_x_333_, lean_object* v_methods_334_, lean_object* v_config_335_, lean_object* v_s_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v_x_333_, v_methods_334_, v_config_335_, v_s_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_344_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run(lean_object* v_00_u03b1_345_, lean_object* v_x_346_, lean_object* v_methods_347_, lean_object* v_config_348_, lean_object* v_s_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v_x_346_, v_methods_347_, v_config_348_, v_s_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimpM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_346_ = stack[1].m_obj;
lean_object* v_methods_347_ = stack[2].m_obj;
lean_object* v_config_348_ = stack[3].m_obj;
lean_object* v_s_349_ = stack[4].m_obj;
lean_object* v_a_350_ = stack[5].m_obj;
lean_object* v_a_351_ = stack[6].m_obj;
lean_object* v_a_352_ = stack[7].m_obj;
lean_object* v_a_353_ = stack[8].m_obj;
lean_object* v_a_354_ = stack[9].m_obj;
lean_object* v_a_355_ = stack[10].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_Meta_Sym_DSimp_DSimpM_run(lean_box(0), v_x_346_, v_methods_347_, v_config_348_, v_s_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___boxed(lean_object* v_00_u03b1_359_, lean_object* v_x_360_, lean_object* v_methods_361_, lean_object* v_config_362_, lean_object* v_s_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Sym_DSimp_DSimpM_run(v_00_u03b1_359_, v_x_360_, v_methods_361_, v_config_362_, v_s_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
return v___x_377_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(lean_object* v_x_378_, lean_object* v_methods_379_, lean_object* v_config_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2);
v___x_389_ = lean_st_mk_ref(v___x_388_);
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
lean_inc_ref(v_a_383_);
lean_inc(v_a_382_);
lean_inc_ref(v_a_381_);
lean_inc(v___x_389_);
v___x_390_ = lean_apply_10(v_x_378_, v_methods_379_, v_config_380_, v___x_389_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, lean_box(0));
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_399_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_399_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_st_ref_get(v___x_389_);
lean_dec(v___x_389_);
lean_dec(v___x_395_);
if (v_isShared_394_ == 0)
{
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_391_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_dec(v___x_389_);
return v___x_390_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_378_ = stack[0].m_obj;
lean_object* v_methods_379_ = stack[1].m_obj;
lean_object* v_config_380_ = stack[2].m_obj;
lean_object* v_a_381_ = stack[3].m_obj;
lean_object* v_a_382_ = stack[4].m_obj;
lean_object* v_a_383_ = stack[5].m_obj;
lean_object* v_a_384_ = stack[6].m_obj;
lean_object* v_a_385_ = stack[7].m_obj;
lean_object* v_a_386_ = stack[8].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_378_, v_methods_379_, v_config_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___boxed(lean_object* v_x_401_, lean_object* v_methods_402_, lean_object* v_config_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_401_, v_methods_402_, v_config_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_411_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(lean_object* v_00_u03b1_412_, lean_object* v_x_413_, lean_object* v_methods_414_, lean_object* v_config_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_413_, v_methods_414_, v_config_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
return v___x_423_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimpM_run_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_413_ = stack[1].m_obj;
lean_object* v_methods_414_ = stack[2].m_obj;
lean_object* v_config_415_ = stack[3].m_obj;
lean_object* v_a_416_ = stack[4].m_obj;
lean_object* v_a_417_ = stack[5].m_obj;
lean_object* v_a_418_ = stack[6].m_obj;
lean_object* v_a_419_ = stack[7].m_obj;
lean_object* v_a_420_ = stack[8].m_obj;
lean_object* v_a_421_ = stack[9].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(lean_box(0), v_x_413_, v_methods_414_, v_config_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___boxed(lean_object* v_00_u03b1_425_, lean_object* v_x_426_, lean_object* v_methods_427_, lean_object* v_config_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(v_00_u03b1_425_, v_x_426_, v_methods_427_, v_config_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_436_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimp_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_437_ = stack[0].m_obj;
lean_object* v_a_438_ = stack[1].m_obj;
lean_object* v_a_439_ = stack[2].m_obj;
lean_object* v_a_440_ = stack[3].m_obj;
lean_object* v_a_441_ = stack[4].m_obj;
lean_object* v_a_442_ = stack[5].m_obj;
lean_object* v_a_443_ = stack[6].m_obj;
lean_object* v_a_444_ = stack[7].m_obj;
lean_object* v_a_445_ = stack[8].m_obj;
lean_object* v_a_446_ = stack[9].m_obj;
lean_object* v_res_448_;
v_res_448_ = lean_sym_dsimp(v_a_00___x40___internal___hyg_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object* v_a_00___x40___internal___hyg_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_00___x40___internal___hyg_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = lean_sym_dsimp(v_a_00___x40___internal___hyg_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
return v_res_460_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg(lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; 
lean_inc_ref(v_a_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_a_461_);
return v___x_463_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_getConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_461_ = stack[0].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Lean_Meta_Sym_DSimp_getConfig___redArg(v_a_461_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg___boxed(lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Sym_DSimp_getConfig___redArg(v_a_465_);
lean_dec_ref(v_a_465_);
return v_res_467_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_getConfig(lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; 
lean_inc_ref(v_a_469_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_a_469_);
return v___x_478_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_getConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_468_ = stack[0].m_obj;
lean_object* v_a_469_ = stack[1].m_obj;
lean_object* v_a_470_ = stack[2].m_obj;
lean_object* v_a_471_ = stack[3].m_obj;
lean_object* v_a_472_ = stack[4].m_obj;
lean_object* v_a_473_ = stack[5].m_obj;
lean_object* v_a_474_ = stack[6].m_obj;
lean_object* v_a_475_ = stack[7].m_obj;
lean_object* v_a_476_ = stack[8].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Lean_Meta_Sym_DSimp_getConfig(v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___boxed(lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Sym_DSimp_getConfig(v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
return v_res_490_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_pre(lean_object* v_e_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_pre_502_; lean_object* v___x_503_; 
v_pre_502_ = lean_ctor_get(v_a_492_, 0);
lean_inc_ref(v_pre_502_);
lean_inc(v_a_500_);
lean_inc_ref(v_a_499_);
lean_inc(v_a_498_);
lean_inc_ref(v_a_497_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc(v_a_492_);
v___x_503_ = lean_apply_11(v_pre_502_, v_e_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, lean_box(0));
return v___x_503_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_pre_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_491_ = stack[0].m_obj;
lean_object* v_a_492_ = stack[1].m_obj;
lean_object* v_a_493_ = stack[2].m_obj;
lean_object* v_a_494_ = stack[3].m_obj;
lean_object* v_a_495_ = stack[4].m_obj;
lean_object* v_a_496_ = stack[5].m_obj;
lean_object* v_a_497_ = stack[6].m_obj;
lean_object* v_a_498_ = stack[7].m_obj;
lean_object* v_a_499_ = stack[8].m_obj;
lean_object* v_a_500_ = stack[9].m_obj;
lean_object* v_res_504_;
v_res_504_ = l_Lean_Meta_Sym_DSimp_pre(v_e_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre___boxed(lean_object* v_e_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Meta_Sym_DSimp_pre(v_e_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
return v_res_516_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_post(lean_object* v_e_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_post_528_; lean_object* v___x_529_; 
v_post_528_ = lean_ctor_get(v_a_518_, 1);
lean_inc_ref(v_post_528_);
lean_inc(v_a_526_);
lean_inc_ref(v_a_525_);
lean_inc(v_a_524_);
lean_inc_ref(v_a_523_);
lean_inc(v_a_522_);
lean_inc_ref(v_a_521_);
lean_inc(v_a_520_);
lean_inc_ref(v_a_519_);
lean_inc(v_a_518_);
v___x_529_ = lean_apply_11(v_post_528_, v_e_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, lean_box(0));
return v___x_529_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_post_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_517_ = stack[0].m_obj;
lean_object* v_a_518_ = stack[1].m_obj;
lean_object* v_a_519_ = stack[2].m_obj;
lean_object* v_a_520_ = stack[3].m_obj;
lean_object* v_a_521_ = stack[4].m_obj;
lean_object* v_a_522_ = stack[5].m_obj;
lean_object* v_a_523_ = stack[6].m_obj;
lean_object* v_a_524_ = stack[7].m_obj;
lean_object* v_a_525_ = stack[8].m_obj;
lean_object* v_a_526_ = stack[9].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Meta_Sym_DSimp_post(v_e_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post___boxed(lean_object* v_e_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Sym_DSimp_post(v_e_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
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
lean_object* l_Lean_Meta_Sym_dsimp(lean_object* v_e_543_, lean_object* v_methods_544_, lean_object* v_config_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_e_543_);
v___x_553_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_553_, 0, v_e_543_);
v___x_554_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v___x_553_, v_methods_544_, v_config_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_566_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
if (lean_obj_tag(v_a_555_) == 0)
{
lean_object* v___x_560_; 
lean_dec_ref_known(v_a_555_, 0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_e_543_);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_e_543_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v_e_x27_562_; lean_object* v___x_564_; 
lean_dec_ref(v_e_543_);
v_e_x27_562_ = lean_ctor_get(v_a_555_, 0);
lean_inc_ref(v_e_x27_562_);
lean_dec_ref_known(v_a_555_, 1);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_e_x27_562_);
v___x_564_ = v___x_557_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_e_x27_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_e_543_);
v_a_567_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_554_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_dsimp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_543_ = stack[0].m_obj;
lean_object* v_methods_544_ = stack[1].m_obj;
lean_object* v_config_545_ = stack[2].m_obj;
lean_object* v_a_546_ = stack[3].m_obj;
lean_object* v_a_547_ = stack[4].m_obj;
lean_object* v_a_548_ = stack[5].m_obj;
lean_object* v_a_549_ = stack[6].m_obj;
lean_object* v_a_550_ = stack[7].m_obj;
lean_object* v_a_551_ = stack[8].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Meta_Sym_dsimp(v_e_543_, v_methods_544_, v_config_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp___boxed(lean_object* v_e_576_, lean_object* v_methods_577_, lean_object* v_config_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Sym_dsimp(v_e_576_, v_methods_577_, v_config_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_586_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
