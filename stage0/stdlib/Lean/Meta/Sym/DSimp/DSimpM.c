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
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg(){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg___boxed(lean_object* v___dummy_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(lean_object* v_00_u03b1_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0, &l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0));
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed(lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(v_x_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v_x_236_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(lean_object* v_m_253_){
_start:
{
lean_inc_ref(v_m_253_);
return v_m_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl___boxed(lean_object* v_m_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(v_m_254_);
lean_dec_ref(v_m_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(lean_object* v_m_256_){
_start:
{
lean_inc(v_m_256_);
return v_m_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl___boxed(lean_object* v_m_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(v_m_257_);
lean_dec(v_m_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg(lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; 
lean_inc(v_a_259_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___redArg___boxed(lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Sym_DSimp_getMethods___redArg(v_a_262_);
lean_dec(v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc(v_a_265_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_a_265_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getMethods___boxed(lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_Sym_DSimp_getMethods(v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
return v_res_286_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__0, &l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__0);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object* v_x_290_, lean_object* v_methods_291_, lean_object* v_config_292_, lean_object* v_s_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_cache_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_330_; 
v_cache_301_ = lean_ctor_get(v_s_293_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_s_293_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_331_ = lean_ctor_get(v_s_293_, 2);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_s_293_, 0);
lean_dec(v_unused_332_);
v___x_303_ = v_s_293_;
v_isShared_304_ = v_isSharedCheck_330_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_cache_301_);
lean_dec(v_s_293_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_330_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 2, v___x_306_);
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_cache_301_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_306_);
v___x_308_ = v_reuseFailAlloc_329_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_st_mk_ref(v___x_308_);
lean_inc(v_a_299_);
lean_inc_ref(v_a_298_);
lean_inc(v_a_297_);
lean_inc_ref(v_a_296_);
lean_inc(v_a_295_);
lean_inc_ref(v_a_294_);
lean_inc(v___x_309_);
v___x_310_ = lean_apply_10(v_x_290_, v_methods_291_, v_config_292_, v___x_309_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run(lean_object* v_00_u03b1_345_, lean_object* v_x_346_, lean_object* v_methods_347_, lean_object* v_config_348_, lean_object* v_s_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v_x_346_, v_methods_347_, v_config_348_, v_s_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___boxed(lean_object* v_00_u03b1_358_, lean_object* v_x_359_, lean_object* v_methods_360_, lean_object* v_config_361_, lean_object* v_s_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Sym_DSimp_DSimpM_run(v_00_u03b1_358_, v_x_359_, v_methods_360_, v_config_361_, v_s_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_370_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1, &l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___closed__1);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(lean_object* v_x_374_, lean_object* v_methods_375_, lean_object* v_config_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0, &l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0);
v___x_385_ = lean_st_mk_ref(v___x_384_);
lean_inc(v_a_382_);
lean_inc_ref(v_a_381_);
lean_inc(v_a_380_);
lean_inc_ref(v_a_379_);
lean_inc(v_a_378_);
lean_inc_ref(v_a_377_);
lean_inc(v___x_385_);
v___x_386_ = lean_apply_10(v_x_374_, v_methods_375_, v_config_376_, v___x_385_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, lean_box(0));
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_395_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_st_ref_get(v___x_385_);
lean_dec(v___x_385_);
lean_dec(v___x_391_);
if (v_isShared_390_ == 0)
{
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_387_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_dec(v___x_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___boxed(lean_object* v_x_396_, lean_object* v_methods_397_, lean_object* v_config_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_396_, v_methods_397_, v_config_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(lean_object* v_00_u03b1_407_, lean_object* v_x_408_, lean_object* v_methods_409_, lean_object* v_config_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v_x_408_, v_methods_409_, v_config_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___boxed(lean_object* v_00_u03b1_419_, lean_object* v_x_420_, lean_object* v_methods_421_, lean_object* v_config_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(v_00_u03b1_419_, v_x_420_, v_methods_421_, v_config_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object* v_a_00___x40___internal___hyg_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_00___x40___internal___hyg_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = lean_sym_dsimp(v_a_00___x40___internal___hyg_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg(lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; 
lean_inc_ref(v_a_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v_a_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___redArg___boxed(lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_Sym_DSimp_getConfig___redArg(v_a_457_);
lean_dec_ref(v_a_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig(lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; 
lean_inc_ref(v_a_461_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_a_461_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getConfig___boxed(lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_Sym_DSimp_getConfig(v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_pre_493_; lean_object* v___x_494_; 
v_pre_493_ = lean_ctor_get(v_a_483_, 0);
lean_inc_ref(v_pre_493_);
lean_inc(v_a_491_);
lean_inc_ref(v_a_490_);
lean_inc(v_a_489_);
lean_inc_ref(v_a_488_);
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
lean_inc(v_a_485_);
lean_inc_ref(v_a_484_);
lean_inc(v_a_483_);
v___x_494_ = lean_apply_11(v_pre_493_, v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, lean_box(0));
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_pre___boxed(lean_object* v_e_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Sym_DSimp_pre(v_e_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post(lean_object* v_e_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_post_518_; lean_object* v___x_519_; 
v_post_518_ = lean_ctor_get(v_a_508_, 1);
lean_inc_ref(v_post_518_);
lean_inc(v_a_516_);
lean_inc_ref(v_a_515_);
lean_inc(v_a_514_);
lean_inc_ref(v_a_513_);
lean_inc(v_a_512_);
lean_inc_ref(v_a_511_);
lean_inc(v_a_510_);
lean_inc_ref(v_a_509_);
lean_inc(v_a_508_);
v___x_519_ = lean_apply_11(v_post_518_, v_e_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, lean_box(0));
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_post___boxed(lean_object* v_e_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Meta_Sym_DSimp_post(v_e_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp(lean_object* v_e_532_, lean_object* v_methods_533_, lean_object* v_config_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc_ref(v_e_532_);
v___x_542_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_542_, 0, v_e_532_);
v___x_543_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(v___x_542_, v_methods_533_, v_config_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_555_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
if (lean_obj_tag(v_a_544_) == 0)
{
lean_object* v___x_549_; 
lean_dec_ref_known(v_a_544_, 0);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v_e_532_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_e_532_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v_e_x27_551_; lean_object* v___x_553_; 
lean_dec_ref(v_e_532_);
v_e_x27_551_ = lean_ctor_get(v_a_544_, 0);
lean_inc_ref(v_e_x27_551_);
lean_dec_ref_known(v_a_544_, 1);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v_e_x27_551_);
v___x_553_ = v___x_546_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_e_x27_551_);
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
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_e_532_);
v_a_556_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_543_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_543_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_dsimp___boxed(lean_object* v_e_564_, lean_object* v_methods_565_, lean_object* v_config_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_Sym_dsimp(v_e_564_, v_methods_565_, v_config_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
return v_res_574_;
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
