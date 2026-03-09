// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Basic
// Imports: public import Lean.Meta.ForEachExpr
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__4_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__5_value;
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__6;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__7;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__8;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__9;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__10;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__11;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__12;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__13;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__14;
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__15 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__15_value;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__16 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__16_value;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__17 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__17_value;
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__18;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__19;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__20;
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__21;
static const lean_string_object l_Lean_Elab_Structural_instInhabitedM___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__22 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__22_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__23;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedM(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value;
lean_object* l_Array_range(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4;
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value;
lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_blt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value;
lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value;
lean_object* l_panic___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Structural.Positions.mapMwith"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: positions.size = ys.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: positions.numIndices = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5;
static const lean_array_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6_value;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 93, 210, 117, 29, 155, 126, 189)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 202, 50, 112, 18, 212, 25, 136)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 23, 214, 102, 176, 92, 61, 7)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 242, 64, 13, 155, 86, 160, 173)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 198, 105, 72, 111, 167, 237, 39)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 69, 67, 115, 43, 149, 20, 105)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 31, 132, 210, 180, 148, 101, 30)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 98, 226, 195, 133, 57, 212, 22)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 87, 212, 210, 179, 92, 88, 148)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2093547783) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(133, 199, 80, 82, 103, 156, 192, 18)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 239, 117, 197, 243, 90, 72, 42)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 62, 224, 211, 204, 80, 164, 101)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(83, 62, 38, 220, 18, 160, 27, 136)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__0, &l_Lean_Elab_Structural_instInhabitedM___closed__0_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__0);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__7, &l_Lean_Elab_Structural_instInhabitedM___closed__7_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__7);
x_2 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__6, &l_Lean_Elab_Structural_instInhabitedM___closed__6_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__6);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__8, &l_Lean_Elab_Structural_instInhabitedM___closed__8_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__8);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__8, &l_Lean_Elab_Structural_instInhabitedM___closed__8_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__8);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__10, &l_Lean_Elab_Structural_instInhabitedM___closed__10_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__10);
x_2 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__9, &l_Lean_Elab_Structural_instInhabitedM___closed__9_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__9);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__11, &l_Lean_Elab_Structural_instInhabitedM___closed__11_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__11);
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__11, &l_Lean_Elab_Structural_instInhabitedM___closed__11_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__11);
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__13, &l_Lean_Elab_Structural_instInhabitedM___closed__13_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__13);
x_2 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__12, &l_Lean_Elab_Structural_instInhabitedM___closed__12_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__12);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_instMonadQuotationCoreM;
x_2 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__16));
x_3 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__15));
x_4 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__18, &l_Lean_Elab_Structural_instInhabitedM___closed__18_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__18);
x_2 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__17));
x_3 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__15));
x_4 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__19, &l_Lean_Elab_Structural_instInhabitedM___closed__19_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__19);
x_2 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__16));
x_3 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__15));
x_4 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__16));
x_2 = l_Lean_Meta_instAddMessageContextMetaM;
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__22));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_69; 
x_2 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__1, &l_Lean_Elab_Structural_instInhabitedM___closed__1_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__1);
x_3 = lean_ctor_get(x_2, 0);
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_2, 1);
lean_dec(x_70);
x_4 = x_2;
x_5 = x_69;
goto block_68;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_3, 1);
lean_dec(x_67);
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__2));
x_13 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__3));
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_8);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_19, 0, x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_17);
lean_ctor_set(x_10, 3, x_18);
lean_ctor_set(x_10, 2, x_19);
lean_ctor_set(x_10, 1, x_12);
lean_ctor_set(x_10, 0, x_16);
x_20 = x_10;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_16);
lean_ctor_set(x_64, 1, x_12);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_18);
lean_ctor_set(x_64, 4, x_17);
x_20 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_21; 
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_20);
x_21 = x_4;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_20);
lean_ctor_set(x_62, 1, x_13);
x_21 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_59; 
x_22 = l_ReaderT_instMonad___redArg(x_21);
x_23 = lean_ctor_get(x_22, 0);
x_59 = !lean_is_exclusive(x_22);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_22, 1);
lean_dec(x_60);
x_24 = x_22;
x_25 = x_59;
goto block_58;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_56; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 2);
x_28 = lean_ctor_get(x_23, 3);
x_29 = lean_ctor_get(x_23, 4);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_23, 1);
lean_dec(x_57);
x_30 = x_23;
x_31 = x_56;
goto block_55;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__4));
x_33 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__5));
lean_inc_ref(x_26);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_26);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_29);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_28);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_39, 0, x_27);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_37);
lean_ctor_set(x_30, 3, x_38);
lean_ctor_set(x_30, 2, x_39);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_36);
x_40 = x_30;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_32);
lean_ctor_set(x_54, 2, x_39);
lean_ctor_set(x_54, 3, x_38);
lean_ctor_set(x_54, 4, x_37);
x_40 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_41; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_33);
lean_ctor_set(x_24, 0, x_40);
x_41 = x_24;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_33);
x_41 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = l_ReaderT_instMonad___redArg(x_41);
x_43 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__14, &l_Lean_Elab_Structural_instInhabitedM___closed__14_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__14);
x_44 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__20, &l_Lean_Elab_Structural_instInhabitedM___closed__20_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__20);
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__21, &l_Lean_Elab_Structural_instInhabitedM___closed__21_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__21);
lean_inc_ref(x_42);
x_47 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_46, x_42);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__23, &l_Lean_Elab_Structural_instInhabitedM___closed__23_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__23);
x_50 = l_Lean_throwError___redArg(x_42, x_48, x_49);
return x_50;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_st_mk_ref(x_2);
lean_inc(x_8);
x_9 = lean_apply_6(x_1, x_8, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_19; 
x_10 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_11 = x_9;
x_12 = x_19;
goto block_18;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_st_ref_get(x_8);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_14);
x_15 = x_11;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 0);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
x_21 = x_9;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Structural_run___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Structural_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Structural_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_12; 
x_12 = l_Lean_Expr_isAppOf(x_3, x_2);
if (x_12 == 0)
{
x_4 = x_12;
goto block_11;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_getAppNumArgs(x_3);
x_14 = lean_nat_dec_lt(x_1, x_13);
lean_dec(x_13);
x_4 = x_14;
goto block_11;
}
block_11:
{
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Expr_getAppNumArgs(x_3);
x_6 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_Expr_getRevArg_x21(x_3, x_8);
x_10 = l_Lean_Expr_hasLooseBVars(x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_find_expr(x_4, x_3);
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec_ref(x_5);
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_3);
if (x_5 == 0)
{
if (x_4 == 0)
{
return x_2;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(x_1, x_6, x_7, x_2);
return x_8;
}
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(x_1, x_9, x_10, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Structural_Positions_numIndices(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_get_borrowed(x_1, x_2, x_7);
lean_inc(x_8);
x_9 = lean_apply_1(x_3, x_8);
x_10 = lean_apply_2(x_4, x_9, x_5);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_dec(x_7);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = lean_array_push(x_6, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_array_get_size(x_1);
x_7 = l_Array_range(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0));
x_11 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
x_12 = lean_nat_dec_lt(x_8, x_9);
if (x_12 == 0)
{
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed), 7, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
x_14 = lean_nat_dec_le(x_9, x_9);
if (x_14 == 0)
{
if (x_12 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_7);
return x_10;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_11, x_13, x_7, x_15, x_16, x_10);
return x_17;
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_9);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_11, x_13, x_7, x_18, x_19, x_10);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(79u);
x_4 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2));
x_5 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_38; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_10 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5));
lean_inc_ref(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1), 5, 4);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_2);
x_12 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
x_13 = lean_array_size(x_5);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_12, x_11, x_13, x_14, x_5);
x_16 = lean_array_get_size(x_4);
lean_dec_ref(x_4);
x_17 = l_Array_range(x_16);
x_47 = lean_unsigned_to_nat(0u);
x_48 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7));
x_49 = lean_array_get_size(x_15);
x_50 = lean_nat_dec_lt(x_47, x_49);
if (x_50 == 0)
{
x_38 = x_48;
goto block_46;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8));
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
if (x_50 == 0)
{
x_38 = x_48;
goto block_46;
}
else
{
size_t x_53; lean_object* x_54; 
x_53 = lean_usize_of_nat(x_49);
lean_inc(x_15);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_12, x_51, x_15, x_14, x_53, x_48);
x_38 = x_54;
goto block_46;
}
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_49);
lean_inc(x_15);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_12, x_51, x_15, x_14, x_55, x_48);
x_38 = x_56;
goto block_46;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0);
x_7 = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4);
x_8 = l_panic___redArg(x_6, x_7);
return x_8;
}
block_23:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_get_size(x_17);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_15);
goto block_9;
}
else
{
uint8_t x_22; 
x_22 = l_Array_isEqvAux___redArg(x_17, x_18, x_10, x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
if (x_22 == 0)
{
lean_dec(x_15);
goto block_9;
}
else
{
return x_15;
}
}
}
block_30:
{
lean_object* x_29; 
x_29 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), x_26, x_25, x_24, x_27, x_28, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_28);
lean_dec(x_25);
x_18 = x_29;
goto block_23;
}
block_37:
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_35, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_inc(x_35);
x_24 = x_32;
x_25 = x_31;
x_26 = x_33;
x_27 = x_35;
x_28 = x_35;
goto block_30;
}
else
{
x_24 = x_32;
x_25 = x_31;
x_26 = x_33;
x_27 = x_35;
x_28 = x_34;
goto block_30;
}
}
block_46:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_array_get_size(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6));
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_39, x_43);
x_45 = lean_nat_dec_le(x_40, x_44);
if (x_45 == 0)
{
lean_inc(x_44);
x_31 = x_39;
x_32 = x_38;
x_33 = x_42;
x_34 = x_44;
x_35 = x_44;
goto block_37;
}
else
{
x_31 = x_39;
x_32 = x_38;
x_33 = x_42;
x_34 = x_44;
x_35 = x_40;
goto block_37;
}
}
else
{
x_18 = x_38;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Structural_Positions_groupAndSort___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_1, x_6, x_7, x_4);
x_9 = lean_apply_2(x_2, x_3, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(89u);
x_4 = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
x_5 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(90u);
x_4 = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
x_5 = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0);
x_11 = l_instInhabitedOfMonad___redArg(x_1, x_10);
x_12 = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3);
x_13 = l_panic___redArg(x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Elab_Structural_Positions_numIndices(x_4);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0);
x_18 = l_instInhabitedOfMonad___redArg(x_1, x_17);
x_19 = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5);
x_20 = l_panic___redArg(x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1), 4, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_3);
x_23 = lean_unsigned_to_nat(0u);
x_24 = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6));
x_25 = l_Array_zipWithMAux___redArg(x_1, x_5, x_4, x_22, x_23, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Structural_Positions_mapMwith___redArg(x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_ForEachExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ForEachExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
