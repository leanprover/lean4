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
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__1;
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__2_value;
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__3_value;
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__4_value;
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__6;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__7;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__8;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__9;
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
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__15 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__15_value;
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__16 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__16_value;
static const lean_closure_object l_Lean_Elab_Structural_instInhabitedM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__17 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__18;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__19;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__20;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__21;
static const lean_string_object l_Lean_Elab_Structural_instInhabitedM___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__22 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedM___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_blt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value;
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__0, &l_Lean_Elab_Structural_instInhabitedM___closed__0_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__0);
v___x_3_ = l_ReaderT_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__6(void){
_start:
{
lean_object* v___x_8_; lean_object* v___f_9_; 
v___x_8_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_9_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_9_, 0, v___x_8_);
return v___f_9_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__7(void){
_start:
{
lean_object* v___x_10_; lean_object* v___f_11_; 
v___x_10_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_11_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_11_, 0, v___x_10_);
return v___f_11_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__8(void){
_start:
{
lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
v___f_12_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__7, &l_Lean_Elab_Structural_instInhabitedM___closed__7_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__7);
v___f_13_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__6, &l_Lean_Elab_Structural_instInhabitedM___closed__6_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__6);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___f_13_);
lean_ctor_set(v___x_14_, 1, v___f_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__9(void){
_start:
{
lean_object* v___x_15_; lean_object* v___f_16_; 
v___x_15_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__8, &l_Lean_Elab_Structural_instInhabitedM___closed__8_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__8);
v___f_16_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_16_, 0, v___x_15_);
return v___f_16_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__10(void){
_start:
{
lean_object* v___x_17_; lean_object* v___f_18_; 
v___x_17_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__8, &l_Lean_Elab_Structural_instInhabitedM___closed__8_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__8);
v___f_18_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_18_, 0, v___x_17_);
return v___f_18_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__11(void){
_start:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; 
v___f_19_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__10, &l_Lean_Elab_Structural_instInhabitedM___closed__10_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__10);
v___f_20_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__9, &l_Lean_Elab_Structural_instInhabitedM___closed__9_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__9);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___f_20_);
lean_ctor_set(v___x_21_, 1, v___f_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__12(void){
_start:
{
lean_object* v___x_22_; lean_object* v___f_23_; 
v___x_22_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__11, &l_Lean_Elab_Structural_instInhabitedM___closed__11_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__11);
v___f_23_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_23_, 0, v___x_22_);
return v___f_23_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__13(void){
_start:
{
lean_object* v___x_24_; lean_object* v___f_25_; 
v___x_24_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__11, &l_Lean_Elab_Structural_instInhabitedM___closed__11_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__11);
v___f_25_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_25_, 0, v___x_24_);
return v___f_25_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__14(void){
_start:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v___f_26_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__13, &l_Lean_Elab_Structural_instInhabitedM___closed__13_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__13);
v___f_27_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__12, &l_Lean_Elab_Structural_instInhabitedM___closed__12_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__12);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___f_27_);
lean_ctor_set(v___x_28_, 1, v___f_26_);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__18(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___f_34_; lean_object* v___x_35_; 
v___x_32_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_33_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__16));
v___f_34_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__15));
v___x_35_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_34_, v___x_33_, v___x_32_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__19(void){
_start:
{
lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v___x_36_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__18, &l_Lean_Elab_Structural_instInhabitedM___closed__18_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__18);
v___f_37_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__17));
v___f_38_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__15));
v___x_39_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_38_, v___f_37_, v___x_36_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__20(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v___x_40_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__19, &l_Lean_Elab_Structural_instInhabitedM___closed__19_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__19);
v___x_41_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__16));
v___f_42_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__15));
v___x_43_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_42_, v___x_41_, v___x_40_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__21(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___f_46_; 
v___x_44_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__16));
v___x_45_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_46_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_46_, 0, v___x_45_);
lean_closure_set(v___f_46_, 1, v___x_44_);
return v___f_46_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__23(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__22));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedM(lean_object* v_00_u03b1_50_){
_start:
{
lean_object* v___x_51_; lean_object* v_toApplicative_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_118_; 
v___x_51_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__1, &l_Lean_Elab_Structural_instInhabitedM___closed__1_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__1);
v_toApplicative_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v___x_51_, 1);
lean_dec(v_unused_119_);
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_118_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_toApplicative_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_118_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v_toFunctor_56_; lean_object* v_toSeq_57_; lean_object* v_toSeqLeft_58_; lean_object* v_toSeqRight_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_116_; 
v_toFunctor_56_ = lean_ctor_get(v_toApplicative_52_, 0);
v_toSeq_57_ = lean_ctor_get(v_toApplicative_52_, 2);
v_toSeqLeft_58_ = lean_ctor_get(v_toApplicative_52_, 3);
v_toSeqRight_59_ = lean_ctor_get(v_toApplicative_52_, 4);
v_isSharedCheck_116_ = !lean_is_exclusive(v_toApplicative_52_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v_toApplicative_52_, 1);
lean_dec(v_unused_117_);
v___x_61_ = v_toApplicative_52_;
v_isShared_62_ = v_isSharedCheck_116_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_toSeqRight_59_);
lean_inc(v_toSeqLeft_58_);
lean_inc(v_toSeq_57_);
lean_inc(v_toFunctor_56_);
lean_dec(v_toApplicative_52_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_116_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___f_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___x_72_; 
v___f_63_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__2));
v___f_64_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__3));
lean_inc_ref(v_toFunctor_56_);
v___f_65_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_65_, 0, v_toFunctor_56_);
v___f_66_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_66_, 0, v_toFunctor_56_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___f_65_);
lean_ctor_set(v___x_67_, 1, v___f_66_);
v___f_68_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_68_, 0, v_toSeqRight_59_);
v___f_69_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_69_, 0, v_toSeqLeft_58_);
v___f_70_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_70_, 0, v_toSeq_57_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 4, v___f_68_);
lean_ctor_set(v___x_61_, 3, v___f_69_);
lean_ctor_set(v___x_61_, 2, v___f_70_);
lean_ctor_set(v___x_61_, 1, v___f_63_);
lean_ctor_set(v___x_61_, 0, v___x_67_);
v___x_72_ = v___x_61_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___f_63_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v___f_70_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v___f_69_);
lean_ctor_set(v_reuseFailAlloc_115_, 4, v___f_68_);
v___x_72_ = v_reuseFailAlloc_115_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 1, v___f_64_);
lean_ctor_set(v___x_54_, 0, v___x_72_);
v___x_74_ = v___x_54_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___f_64_);
v___x_74_ = v_reuseFailAlloc_114_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v_toApplicative_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_112_; 
v___x_75_ = l_ReaderT_instMonad___redArg(v___x_74_);
v_toApplicative_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v___x_75_, 1);
lean_dec(v_unused_113_);
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_112_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_toApplicative_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_112_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_toFunctor_80_; lean_object* v_toSeq_81_; lean_object* v_toSeqLeft_82_; lean_object* v_toSeqRight_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_110_; 
v_toFunctor_80_ = lean_ctor_get(v_toApplicative_76_, 0);
v_toSeq_81_ = lean_ctor_get(v_toApplicative_76_, 2);
v_toSeqLeft_82_ = lean_ctor_get(v_toApplicative_76_, 3);
v_toSeqRight_83_ = lean_ctor_get(v_toApplicative_76_, 4);
v_isSharedCheck_110_ = !lean_is_exclusive(v_toApplicative_76_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v_toApplicative_76_, 1);
lean_dec(v_unused_111_);
v___x_85_ = v_toApplicative_76_;
v_isShared_86_ = v_isSharedCheck_110_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_toSeqRight_83_);
lean_inc(v_toSeqLeft_82_);
lean_inc(v_toSeq_81_);
lean_inc(v_toFunctor_80_);
lean_dec(v_toApplicative_76_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_110_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_96_; 
v___f_87_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__4));
v___f_88_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedM___closed__5));
lean_inc_ref(v_toFunctor_80_);
v___f_89_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_89_, 0, v_toFunctor_80_);
v___f_90_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_90_, 0, v_toFunctor_80_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___f_89_);
lean_ctor_set(v___x_91_, 1, v___f_90_);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_92_, 0, v_toSeqRight_83_);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_93_, 0, v_toSeqLeft_82_);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_94_, 0, v_toSeq_81_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 4, v___f_92_);
lean_ctor_set(v___x_85_, 3, v___f_93_);
lean_ctor_set(v___x_85_, 2, v___f_94_);
lean_ctor_set(v___x_85_, 1, v___f_87_);
lean_ctor_set(v___x_85_, 0, v___x_91_);
v___x_96_ = v___x_85_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v___f_94_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v___f_93_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v___f_92_);
v___x_96_ = v_reuseFailAlloc_109_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___f_88_);
lean_ctor_set(v___x_78_, 0, v___x_96_);
v___x_98_ = v___x_78_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___f_88_);
v___x_98_ = v_reuseFailAlloc_108_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_toMonadRef_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_99_ = l_ReaderT_instMonad___redArg(v___x_98_);
v___x_100_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__14, &l_Lean_Elab_Structural_instInhabitedM___closed__14_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__14);
v___x_101_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__20, &l_Lean_Elab_Structural_instInhabitedM___closed__20_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__20);
v_toMonadRef_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_toMonadRef_102_);
v___f_103_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__21, &l_Lean_Elab_Structural_instInhabitedM___closed__21_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__21);
lean_inc_ref(v___x_99_);
v___x_104_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_103_, v___x_99_);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_100_);
lean_ctor_set(v___x_105_, 1, v_toMonadRef_102_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
v___x_106_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedM___closed__23, &l_Lean_Elab_Structural_instInhabitedM___closed__23_once, _init_l_Lean_Elab_Structural_instInhabitedM___closed__23);
v___x_107_ = l_Lean_throwError___redArg(v___x_99_, v___x_105_, v___x_106_);
return v___x_107_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg(lean_object* v_x_120_, lean_object* v_s_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_st_mk_ref(v_s_121_);
lean_inc(v___x_127_);
v___x_128_ = lean_apply_6(v_x_120_, v___x_127_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, lean_box(0));
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_138_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_138_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_138_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_138_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_st_ref_get(v___x_127_);
lean_dec(v___x_127_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_a_129_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_134_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v___x_127_);
v_a_139_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_128_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_128_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___redArg___boxed(lean_object* v_x_147_, lean_object* v_s_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_Structural_run___redArg(v_x_147_, v_s_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run(lean_object* v_00_u03b1_155_, lean_object* v_x_156_, lean_object* v_s_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Elab_Structural_run___redArg(v_x_156_, v_s_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_run___boxed(lean_object* v_00_u03b1_164_, lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Elab_Structural_run(v_00_u03b1_164_, v_x_165_, v_s_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object* v_recArgPos_173_, lean_object* v_recFnName_174_, lean_object* v_e_175_){
_start:
{
uint8_t v___y_177_; uint8_t v___x_184_; 
v___x_184_ = l_Lean_Expr_isAppOf(v_e_175_, v_recFnName_174_);
if (v___x_184_ == 0)
{
v___y_177_ = v___x_184_;
goto v___jp_176_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = l_Lean_Expr_getAppNumArgs(v_e_175_);
v___x_186_ = lean_nat_dec_lt(v_recArgPos_173_, v___x_185_);
lean_dec(v___x_185_);
v___y_177_ = v___x_186_;
goto v___jp_176_;
}
v___jp_176_:
{
if (v___y_177_ == 0)
{
return v___y_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_178_ = l_Lean_Expr_getAppNumArgs(v_e_175_);
v___x_179_ = lean_nat_sub(v___x_178_, v_recArgPos_173_);
lean_dec(v___x_178_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_sub(v___x_179_, v___x_180_);
lean_dec(v___x_179_);
v___x_182_ = l_Lean_Expr_getRevArg_x21(v_e_175_, v___x_181_);
v___x_183_ = l_Lean_Expr_hasLooseBVars(v___x_182_);
lean_dec_ref(v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object* v_recArgPos_187_, lean_object* v_recFnName_188_, lean_object* v_e_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(v_recArgPos_187_, v_recFnName_188_, v_e_189_);
lean_dec_ref(v_e_189_);
lean_dec(v_recFnName_188_);
lean_dec(v_recArgPos_187_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object* v_recFnName_192_, lean_object* v_recArgPos_193_, lean_object* v_e_194_){
_start:
{
lean_object* v___f_195_; lean_object* v_app_x3f_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed), 3, 2);
lean_closure_set(v___f_195_, 0, v_recArgPos_193_);
lean_closure_set(v___f_195_, 1, v_recFnName_192_);
v_app_x3f_196_ = lean_find_expr(v___f_195_, v_e_194_);
lean_dec_ref(v___f_195_);
if (lean_obj_tag(v_app_x3f_196_) == 0)
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
else
{
uint8_t v___x_198_; 
lean_dec_ref(v_app_x3f_196_);
v___x_198_ = 1;
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object* v_recFnName_199_, lean_object* v_recArgPos_200_, lean_object* v_e_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_recFnName_199_, v_recArgPos_200_, v_e_201_);
lean_dec_ref(v_e_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object* v_as_204_, size_t v_i_205_, size_t v_stop_206_, lean_object* v_b_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = lean_usize_dec_eq(v_i_205_, v_stop_206_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; 
v___x_209_ = lean_array_uget_borrowed(v_as_204_, v_i_205_);
v___x_210_ = lean_array_get_size(v___x_209_);
v___x_211_ = lean_nat_add(v_b_207_, v___x_210_);
lean_dec(v_b_207_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_205_, v___x_212_);
v_i_205_ = v___x_213_;
v_b_207_ = v___x_211_;
goto _start;
}
else
{
return v_b_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object* v_as_215_, lean_object* v_i_216_, lean_object* v_stop_217_, lean_object* v_b_218_){
_start:
{
size_t v_i_boxed_219_; size_t v_stop_boxed_220_; lean_object* v_res_221_; 
v_i_boxed_219_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_stop_boxed_220_ = lean_unbox_usize(v_stop_217_);
lean_dec(v_stop_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_as_215_, v_i_boxed_219_, v_stop_boxed_220_, v_b_218_);
lean_dec_ref(v_as_215_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object* v_positions_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_array_get_size(v_positions_222_);
v___x_225_ = lean_nat_dec_lt(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
return v___x_223_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_le(v___x_224_, v___x_224_);
if (v___x_226_ == 0)
{
if (v___x_225_ == 0)
{
return v___x_223_;
}
else
{
size_t v___x_227_; size_t v___x_228_; lean_object* v___x_229_; 
v___x_227_ = ((size_t)0ULL);
v___x_228_ = lean_usize_of_nat(v___x_224_);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_222_, v___x_227_, v___x_228_, v___x_223_);
return v___x_229_;
}
}
else
{
size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v___x_230_ = ((size_t)0ULL);
v___x_231_ = lean_usize_of_nat(v___x_224_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_222_, v___x_230_, v___x_231_, v___x_223_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object* v_positions_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_233_);
lean_dec_ref(v_positions_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object* v_inst_235_, lean_object* v_xs_236_, lean_object* v_f_237_, lean_object* v_inst_238_, lean_object* v_x_239_, lean_object* v_x1_240_, lean_object* v_x2_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_242_ = lean_array_get_borrowed(v_inst_235_, v_xs_236_, v_x2_241_);
lean_inc(v___x_242_);
v___x_243_ = lean_apply_1(v_f_237_, v___x_242_);
v___x_244_ = lean_apply_2(v_inst_238_, v___x_243_, v_x_239_);
v___x_245_ = lean_unbox(v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_x2_241_);
return v_x1_240_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = lean_array_push(v_x1_240_, v_x2_241_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object* v_inst_247_, lean_object* v_xs_248_, lean_object* v_f_249_, lean_object* v_inst_250_, lean_object* v_x_251_, lean_object* v_x1_252_, lean_object* v_x2_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(v_inst_247_, v_xs_248_, v_f_249_, v_inst_250_, v_x_251_, v_x1_252_, v_x2_253_);
lean_dec_ref(v_xs_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object* v_xs_276_, lean_object* v_inst_277_, lean_object* v_f_278_, lean_object* v_inst_279_, lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_281_ = lean_array_get_size(v_xs_276_);
v___x_282_ = l_Array_range(v___x_281_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_array_get_size(v___x_282_);
v___x_285_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0));
v___x_286_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v___x_287_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_287_ == 0)
{
lean_dec_ref(v___x_282_);
lean_dec(v_x_280_);
lean_dec_ref(v_inst_279_);
lean_dec(v_f_278_);
lean_dec(v_inst_277_);
lean_dec_ref(v_xs_276_);
return v___x_285_;
}
else
{
lean_object* v___f_288_; uint8_t v___x_289_; 
v___f_288_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_288_, 0, v_inst_277_);
lean_closure_set(v___f_288_, 1, v_xs_276_);
lean_closure_set(v___f_288_, 2, v_f_278_);
lean_closure_set(v___f_288_, 3, v_inst_279_);
lean_closure_set(v___f_288_, 4, v_x_280_);
v___x_289_ = lean_nat_dec_le(v___x_284_, v___x_284_);
if (v___x_289_ == 0)
{
if (v___x_287_ == 0)
{
lean_dec_ref(v___f_288_);
lean_dec_ref(v___x_282_);
return v___x_285_;
}
else
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((size_t)0ULL);
v___x_291_ = lean_usize_of_nat(v___x_284_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_286_, v___f_288_, v___x_282_, v___x_290_, v___x_291_, v___x_285_);
return v___x_292_;
}
}
else
{
size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_284_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_286_, v___f_288_, v___x_282_, v___x_293_, v___x_294_, v___x_285_);
return v___x_295_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0(void){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Array_instInhabited(lean_box(0));
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_300_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3));
v___x_301_ = lean_unsigned_to_nat(2u);
v___x_302_ = lean_unsigned_to_nat(79u);
v___x_303_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2));
v___x_304_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
v___x_305_ = l_mkPanicMessageWithDecl(v___x_304_, v___x_303_, v___x_302_, v___x_301_, v___x_300_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg(lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_f_313_, lean_object* v_xs_314_, lean_object* v_ys_315_){
_start:
{
lean_object* v___f_320_; lean_object* v___f_321_; lean_object* v___x_322_; size_t v_sz_323_; size_t v___x_324_; lean_object* v_positions_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___y_329_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_349_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___f_320_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5));
lean_inc_ref(v_xs_314_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1), 5, 4);
lean_closure_set(v___f_321_, 0, v_xs_314_);
lean_closure_set(v___f_321_, 1, v_inst_311_);
lean_closure_set(v___f_321_, 2, v_f_313_);
lean_closure_set(v___f_321_, 3, v_inst_312_);
v___x_322_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v_sz_323_ = lean_array_size(v_ys_315_);
v___x_324_ = ((size_t)0ULL);
v_positions_325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_322_, v___f_321_, v_sz_323_, v___x_324_, v_ys_315_);
v___x_326_ = lean_array_get_size(v_xs_314_);
lean_dec_ref(v_xs_314_);
v___x_327_ = l_Array_range(v___x_326_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7));
v___x_359_ = lean_array_get_size(v_positions_325_);
v___x_360_ = lean_nat_dec_lt(v___x_357_, v___x_359_);
if (v___x_360_ == 0)
{
v___y_349_ = v___x_358_;
goto v___jp_348_;
}
else
{
lean_object* v___f_361_; uint8_t v___x_362_; 
v___f_361_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8));
v___x_362_ = lean_nat_dec_le(v___x_359_, v___x_359_);
if (v___x_362_ == 0)
{
if (v___x_360_ == 0)
{
v___y_349_ = v___x_358_;
goto v___jp_348_;
}
else
{
size_t v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_usize_of_nat(v___x_359_);
lean_inc(v_positions_325_);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_322_, v___f_361_, v_positions_325_, v___x_324_, v___x_363_, v___x_358_);
v___y_349_ = v___x_364_;
goto v___jp_348_;
}
}
else
{
size_t v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_usize_of_nat(v___x_359_);
lean_inc(v_positions_325_);
v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_322_, v___f_361_, v_positions_325_, v___x_324_, v___x_365_, v___x_358_);
v___y_349_ = v___x_366_;
goto v___jp_348_;
}
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0);
v___x_318_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4);
v___x_319_ = l_panic___redArg(v___x_317_, v___x_318_);
return v___x_319_;
}
v___jp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_array_get_size(v___x_327_);
v___x_331_ = lean_array_get_size(v___y_329_);
v___x_332_ = lean_nat_dec_eq(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___y_329_);
lean_dec_ref(v___x_327_);
lean_dec(v_positions_325_);
goto v___jp_316_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = l_Array_isEqvAux___redArg(v___x_327_, v___y_329_, v___f_320_, v___x_330_);
lean_dec_ref(v___y_329_);
lean_dec_ref(v___x_327_);
if (v___x_333_ == 0)
{
lean_dec(v_positions_325_);
goto v___jp_316_;
}
else
{
return v_positions_325_;
}
}
}
v___jp_334_:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_336_, v___y_337_, v___y_335_, v___y_338_, v___y_339_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_339_);
lean_dec(v___y_337_);
v___y_329_ = v___x_340_;
goto v___jp_328_;
}
v___jp_341_:
{
uint8_t v___x_347_; 
v___x_347_ = lean_nat_dec_le(v___y_346_, v___y_345_);
if (v___x_347_ == 0)
{
lean_dec(v___y_345_);
lean_inc(v___y_346_);
v___y_335_ = v___y_342_;
v___y_336_ = v___y_343_;
v___y_337_ = v___y_344_;
v___y_338_ = v___y_346_;
v___y_339_ = v___y_346_;
goto v___jp_334_;
}
else
{
v___y_335_ = v___y_342_;
v___y_336_ = v___y_343_;
v___y_337_ = v___y_344_;
v___y_338_ = v___y_346_;
v___y_339_ = v___y_345_;
goto v___jp_334_;
}
}
v___jp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_350_ = lean_array_get_size(v___y_349_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_nat_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_353_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6));
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_sub(v___x_350_, v___x_354_);
v___x_356_ = lean_nat_dec_le(v___x_351_, v___x_355_);
if (v___x_356_ == 0)
{
lean_inc(v___x_355_);
v___y_342_ = v___y_349_;
v___y_343_ = v___x_353_;
v___y_344_ = v___x_350_;
v___y_345_ = v___x_355_;
v___y_346_ = v___x_355_;
goto v___jp_341_;
}
else
{
v___y_342_ = v___y_349_;
v___y_343_ = v___x_353_;
v___y_344_ = v___x_350_;
v___y_345_ = v___x_355_;
v___y_346_ = v___x_351_;
goto v___jp_341_;
}
}
else
{
v___y_329_ = v___y_349_;
goto v___jp_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_f_371_, lean_object* v_xs_372_, lean_object* v_ys_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg(v_inst_369_, v_inst_370_, v_f_371_, v_xs_372_, v_ys_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(lean_object* v_inst_375_, lean_object* v_xs_376_, lean_object* v_x_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_array_get_borrowed(v_inst_375_, v_xs_376_, v_x_377_);
lean_inc(v___x_378_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed(lean_object* v_inst_379_, lean_object* v_xs_380_, lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(v_inst_379_, v_xs_380_, v_x_381_);
lean_dec(v_x_381_);
lean_dec_ref(v_xs_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1(lean_object* v___f_383_, lean_object* v_f_384_, lean_object* v_y_385_, lean_object* v_poss_386_){
_start:
{
lean_object* v___x_387_; size_t v_sz_388_; size_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_387_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v_sz_388_ = lean_array_size(v_poss_386_);
v___x_389_ = ((size_t)0ULL);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_387_, v___f_383_, v_sz_388_, v___x_389_, v_poss_386_);
v___x_391_ = lean_apply_2(v_f_384_, v_y_385_, v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Array_instInhabited(lean_box(0));
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2));
v___x_396_ = lean_unsigned_to_nat(2u);
v___x_397_ = lean_unsigned_to_nat(89u);
v___x_398_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
v___x_399_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
v___x_400_ = l_mkPanicMessageWithDecl(v___x_399_, v___x_398_, v___x_397_, v___x_396_, v___x_395_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4));
v___x_403_ = lean_unsigned_to_nat(2u);
v___x_404_ = lean_unsigned_to_nat(90u);
v___x_405_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
v___x_406_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
v___x_407_ = l_mkPanicMessageWithDecl(v___x_406_, v___x_405_, v___x_404_, v___x_403_, v___x_402_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_f_412_, lean_object* v_positions_413_, lean_object* v_ys_414_, lean_object* v_xs_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_array_get_size(v_positions_413_);
v___x_417_ = lean_array_get_size(v_ys_414_);
v___x_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v_xs_415_);
lean_dec_ref(v_ys_414_);
lean_dec_ref(v_positions_413_);
lean_dec(v_f_412_);
lean_dec(v_inst_411_);
v___x_419_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0);
v___x_420_ = l_instInhabitedOfMonad___redArg(v_inst_410_, v___x_419_);
v___x_421_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3);
v___x_422_ = l_panic___redArg(v___x_420_, v___x_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_423_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_413_);
v___x_424_ = lean_array_get_size(v_xs_415_);
v___x_425_ = lean_nat_dec_eq(v___x_423_, v___x_424_);
lean_dec(v___x_423_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref(v_xs_415_);
lean_dec_ref(v_ys_414_);
lean_dec_ref(v_positions_413_);
lean_dec(v_f_412_);
lean_dec(v_inst_411_);
v___x_426_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0);
v___x_427_ = l_instInhabitedOfMonad___redArg(v_inst_410_, v___x_426_);
v___x_428_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5);
v___x_429_ = l_panic___redArg(v___x_427_, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_430_, 0, v_inst_411_);
lean_closure_set(v___f_430_, 1, v_xs_415_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1), 4, 2);
lean_closure_set(v___f_431_, 0, v___f_430_);
lean_closure_set(v___f_431_, 1, v_f_412_);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6));
v___x_434_ = l_Array_zipWithMAux___redArg(v_inst_410_, v_ys_414_, v_positions_413_, v___f_431_, v___x_432_, v___x_433_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object* v_00_u03b3_435_, lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_m_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_f_441_, lean_object* v_positions_442_, lean_object* v_ys_443_, lean_object* v_xs_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v_inst_439_, v_inst_440_, v_f_441_, v_positions_442_, v_ys_443_, v_xs_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
v___x_518_ = 0;
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
v___x_520_ = l_Lean_registerTraceClass(v___x_517_, v___x_518_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
return v_res_522_;
}
}
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
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
res = initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
