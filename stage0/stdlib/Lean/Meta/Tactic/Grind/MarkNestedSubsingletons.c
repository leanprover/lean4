// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Lean.Meta.Sym.Util import Lean.Meta.Tactic.Grind.Util
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonApp___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_private.Lean.Meta.Tactic.Grind.MarkNestedSubsingletons.0.Lean.Meta.Grind.markNestedSubsingletons.visit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Meta.Tactic.Grind.MarkNestedSubsingletons"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_markNestedSubsingletons___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "grind mark subsingleton"};
static const lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_markNestedSubsingletons___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_markNestedSubsingletons___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object* v_e_13_){
_start:
{
if (lean_obj_tag(v_e_13_) == 4)
{
lean_object* v_declName_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_declName_14_ = lean_ctor_get(v_e_13_, 0);
v___x_15_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3));
v___x_16_ = lean_name_eq(v_declName_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5));
v___x_18_ = lean_name_eq(v_declName_14_, v___x_17_);
return v___x_18_;
}
else
{
return v___x_16_;
}
}
else
{
uint8_t v___x_19_; 
v___x_19_ = 0;
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___boxed(lean_object* v_e_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_e_20_);
lean_dec_ref(v_e_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonApp(lean_object* v_e_23_){
_start:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l_Lean_Expr_getAppFn(v_e_23_);
v___x_25_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v___x_24_);
lean_dec_ref(v___x_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = l_Lean_Expr_getAppNumArgs(v_e_23_);
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
lean_dec(v___x_26_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonApp___boxed(lean_object* v_e_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_29_);
lean_dec_ref(v_e_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_whnfCore(v_e_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_75_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_75_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_75_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_75_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_42_, v_a_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_66_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_66_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_66_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_66_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_Lean_Expr_cleanupAnnotations(v_a_47_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___x_56_);
lean_del_object(v___x_44_);
goto v___jp_51_;
}
else
{
lean_object* v_arg_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_arg_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc_ref(v_arg_58_);
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1));
v___x_61_ = l_Lean_Expr_isConstOf(v___x_59_, v___x_60_);
lean_dec_ref(v___x_59_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_arg_58_);
lean_del_object(v___x_44_);
goto v___jp_51_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_64_; 
lean_del_object(v___x_49_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v_arg_58_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_62_);
v___x_64_ = v___x_44_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
v___jp_51_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_del_object(v___x_44_);
v_a_67_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_46_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_46_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v_a_76_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_41_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_41_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___boxed(lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(v_e_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg(lean_object* v_a_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v_key_94_; lean_object* v_value_95_; lean_object* v_tail_96_; size_t v___x_97_; size_t v___x_98_; uint8_t v___x_99_; 
v_key_94_ = lean_ctor_get(v_x_92_, 0);
v_value_95_ = lean_ctor_get(v_x_92_, 1);
v_tail_96_ = lean_ctor_get(v_x_92_, 2);
v___x_97_ = lean_ptr_addr(v_key_94_);
v___x_98_ = lean_ptr_addr(v_a_91_);
v___x_99_ = lean_usize_dec_eq(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
v_x_92_ = v_tail_96_;
goto _start;
}
else
{
lean_object* v___x_101_; 
lean_inc(v_value_95_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_value_95_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg___boxed(lean_object* v_a_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg(v_a_102_, v_x_103_);
lean_dec(v_x_103_);
lean_dec_ref(v_a_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(lean_object* v_m_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_buckets_107_; lean_object* v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v_fold_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_buckets_107_ = lean_ctor_get(v_m_105_, 1);
v___x_108_ = lean_array_get_size(v_buckets_107_);
v___x_109_ = lean_ptr_addr(v_a_106_);
v___x_110_ = ((size_t)3ULL);
v___x_111_ = lean_usize_shift_right(v___x_109_, v___x_110_);
v___x_112_ = lean_usize_to_uint64(v___x_111_);
v___x_113_ = 32ULL;
v___x_114_ = lean_uint64_shift_right(v___x_112_, v___x_113_);
v_fold_115_ = lean_uint64_xor(v___x_112_, v___x_114_);
v___x_116_ = 16ULL;
v___x_117_ = lean_uint64_shift_right(v_fold_115_, v___x_116_);
v___x_118_ = lean_uint64_xor(v_fold_115_, v___x_117_);
v___x_119_ = lean_uint64_to_usize(v___x_118_);
v___x_120_ = lean_usize_of_nat(v___x_108_);
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_sub(v___x_120_, v___x_121_);
v___x_123_ = lean_usize_land(v___x_119_, v___x_122_);
v___x_124_ = lean_array_uget_borrowed(v_buckets_107_, v___x_123_);
v___x_125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg(v_a_106_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg___boxed(lean_object* v_m_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v_m_126_, v_a_127_);
lean_dec_ref(v_a_127_);
lean_dec_ref(v_m_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___lam__0(lean_object* v_k_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v_b_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; 
lean_inc(v___y_140_);
lean_inc_ref(v___y_139_);
lean_inc(v___y_138_);
lean_inc_ref(v___y_137_);
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
lean_inc(v___y_131_);
lean_inc(v___y_130_);
v___x_142_ = lean_apply_12(v_k_129_, v_b_136_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v_b_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___lam__0(v_k_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v_b_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec(v___y_144_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg(lean_object* v_name_157_, uint8_t v_bi_158_, lean_object* v_type_159_, lean_object* v_k_160_, uint8_t v_kind_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; 
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc(v___y_162_);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_173_, 0, v_k_160_);
lean_closure_set(v___f_173_, 1, v___y_162_);
lean_closure_set(v___f_173_, 2, v___y_163_);
lean_closure_set(v___f_173_, 3, v___y_164_);
lean_closure_set(v___f_173_, 4, v___y_165_);
lean_closure_set(v___f_173_, 5, v___y_166_);
lean_closure_set(v___f_173_, 6, v___y_167_);
v___x_174_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_157_, v_bi_158_, v_type_159_, v___f_173_, v_kind_161_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_174_) == 0)
{
return v___x_174_;
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg___boxed(lean_object* v_name_183_, lean_object* v_bi_184_, lean_object* v_type_185_, lean_object* v_k_186_, lean_object* v_kind_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_bi_boxed_199_; uint8_t v_kind_boxed_200_; lean_object* v_res_201_; 
v_bi_boxed_199_ = lean_unbox(v_bi_184_);
v_kind_boxed_200_ = lean_unbox(v_kind_187_);
v_res_201_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg(v_name_183_, v_bi_boxed_199_, v_type_185_, v_k_186_, v_kind_boxed_200_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
return v_res_201_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_instMonadEIO(lean_box(0));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_toApplicative_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_288_; 
v___x_219_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0);
v___x_220_ = l_StateRefT_x27_instMonad___redArg(v___x_219_);
v_toApplicative_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_220_, 1);
lean_dec(v_unused_289_);
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_288_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_toApplicative_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_288_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_toFunctor_225_; lean_object* v_toSeq_226_; lean_object* v_toSeqLeft_227_; lean_object* v_toSeqRight_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_286_; 
v_toFunctor_225_ = lean_ctor_get(v_toApplicative_221_, 0);
v_toSeq_226_ = lean_ctor_get(v_toApplicative_221_, 2);
v_toSeqLeft_227_ = lean_ctor_get(v_toApplicative_221_, 3);
v_toSeqRight_228_ = lean_ctor_get(v_toApplicative_221_, 4);
v_isSharedCheck_286_ = !lean_is_exclusive(v_toApplicative_221_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_toApplicative_221_, 1);
lean_dec(v_unused_287_);
v___x_230_ = v_toApplicative_221_;
v_isShared_231_ = v_isSharedCheck_286_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_toSeqRight_228_);
lean_inc(v_toSeqLeft_227_);
lean_inc(v_toSeq_226_);
lean_inc(v_toFunctor_225_);
lean_dec(v_toApplicative_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_286_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___x_241_; 
v___f_232_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1));
v___f_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_225_);
v___f_234_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_234_, 0, v_toFunctor_225_);
v___f_235_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_235_, 0, v_toFunctor_225_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___f_234_);
lean_ctor_set(v___x_236_, 1, v___f_235_);
v___f_237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_237_, 0, v_toSeqRight_228_);
v___f_238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_238_, 0, v_toSeqLeft_227_);
v___f_239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_239_, 0, v_toSeq_226_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 4, v___f_237_);
lean_ctor_set(v___x_230_, 3, v___f_238_);
lean_ctor_set(v___x_230_, 2, v___f_239_);
lean_ctor_set(v___x_230_, 1, v___f_232_);
lean_ctor_set(v___x_230_, 0, v___x_236_);
v___x_241_ = v___x_230_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v___f_239_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v___f_238_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v___f_237_);
v___x_241_ = v_reuseFailAlloc_285_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___f_233_);
lean_ctor_set(v___x_223_, 0, v___x_241_);
v___x_243_ = v___x_223_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___f_233_);
v___x_243_ = v_reuseFailAlloc_284_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v_toApplicative_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_282_; 
v___x_244_ = l_StateRefT_x27_instMonad___redArg(v___x_243_);
v_toApplicative_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_244_, 1);
lean_dec(v_unused_283_);
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_282_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_toApplicative_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_282_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_toFunctor_249_; lean_object* v_toSeq_250_; lean_object* v_toSeqLeft_251_; lean_object* v_toSeqRight_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_280_; 
v_toFunctor_249_ = lean_ctor_get(v_toApplicative_245_, 0);
v_toSeq_250_ = lean_ctor_get(v_toApplicative_245_, 2);
v_toSeqLeft_251_ = lean_ctor_get(v_toApplicative_245_, 3);
v_toSeqRight_252_ = lean_ctor_get(v_toApplicative_245_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v_toApplicative_245_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_toApplicative_245_, 1);
lean_dec(v_unused_281_);
v___x_254_ = v_toApplicative_245_;
v_isShared_255_ = v_isSharedCheck_280_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_toSeqRight_252_);
lean_inc(v_toSeqLeft_251_);
lean_inc(v_toSeq_250_);
lean_inc(v_toFunctor_249_);
lean_dec(v_toApplicative_245_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_280_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___x_265_; 
v___f_256_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3));
v___f_257_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4));
lean_inc_ref(v_toFunctor_249_);
v___f_258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_258_, 0, v_toFunctor_249_);
v___f_259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_259_, 0, v_toFunctor_249_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___f_258_);
lean_ctor_set(v___x_260_, 1, v___f_259_);
v___f_261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_261_, 0, v_toSeqRight_252_);
v___f_262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_262_, 0, v_toSeqLeft_251_);
v___f_263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_263_, 0, v_toSeq_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v___f_261_);
lean_ctor_set(v___x_254_, 3, v___f_262_);
lean_ctor_set(v___x_254_, 2, v___f_263_);
lean_ctor_set(v___x_254_, 1, v___f_256_);
lean_ctor_set(v___x_254_, 0, v___x_260_);
v___x_265_ = v___x_254_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___f_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___f_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v___f_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v___f_261_);
v___x_265_ = v_reuseFailAlloc_279_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v___f_257_);
lean_ctor_set(v___x_247_, 0, v___x_265_);
v___x_267_ = v___x_247_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___f_257_);
v___x_267_ = v_reuseFailAlloc_278_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_71351__overap_276_; lean_object* v___x_277_; 
v___x_268_ = l_StateRefT_x27_instMonad___redArg(v___x_267_);
v___x_269_ = l_ReaderT_instMonad___redArg(v___x_268_);
v___x_270_ = l_StateRefT_x27_instMonad___redArg(v___x_269_);
v___x_271_ = l_ReaderT_instMonad___redArg(v___x_270_);
v___x_272_ = l_ReaderT_instMonad___redArg(v___x_271_);
v___x_273_ = l_StateRefT_x27_instMonad___redArg(v___x_272_);
v___x_274_ = l_Lean_instInhabitedExpr;
v___x_275_ = l_instInhabitedOfMonad___redArg(v___x_273_, v___x_274_);
v___x_71351__overap_276_ = lean_panic_fn_borrowed(v___x_275_, v_msg_207_);
lean_dec(v___x_275_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc(v___y_208_);
v___x_277_ = lean_apply_11(v___x_71351__overap_276_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, lean_box(0));
return v___x_277_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___boxed(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec(v___y_291_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10_spec__14___redArg(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
return v_x_303_;
}
else
{
lean_object* v_key_305_; lean_object* v_value_306_; lean_object* v_tail_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_333_; 
v_key_305_ = lean_ctor_get(v_x_304_, 0);
v_value_306_ = lean_ctor_get(v_x_304_, 1);
v_tail_307_ = lean_ctor_get(v_x_304_, 2);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_333_ == 0)
{
v___x_309_ = v_x_304_;
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_tail_307_);
lean_inc(v_value_306_);
lean_inc(v_key_305_);
lean_dec(v_x_304_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_311_ = lean_array_get_size(v_x_303_);
v___x_312_ = lean_ptr_addr(v_key_305_);
v___x_313_ = ((size_t)3ULL);
v___x_314_ = lean_usize_shift_right(v___x_312_, v___x_313_);
v___x_315_ = lean_usize_to_uint64(v___x_314_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_311_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v___x_327_ = lean_array_uget_borrowed(v_x_303_, v___x_326_);
lean_inc(v___x_327_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 2, v___x_327_);
v___x_329_ = v___x_309_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_key_305_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_value_306_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v___x_327_);
v___x_329_ = v_reuseFailAlloc_332_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = lean_array_uset(v_x_303_, v___x_326_, v___x_329_);
v_x_303_ = v___x_330_;
v_x_304_ = v_tail_307_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10___redArg(lean_object* v_i_334_, lean_object* v_source_335_, lean_object* v_target_336_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_array_get_size(v_source_335_);
v___x_338_ = lean_nat_dec_lt(v_i_334_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_source_335_);
lean_dec(v_i_334_);
return v_target_336_;
}
else
{
lean_object* v_es_339_; lean_object* v___x_340_; lean_object* v_source_341_; lean_object* v_target_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_es_339_ = lean_array_fget(v_source_335_, v_i_334_);
v___x_340_ = lean_box(0);
v_source_341_ = lean_array_fset(v_source_335_, v_i_334_, v___x_340_);
v_target_342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10_spec__14___redArg(v_target_336_, v_es_339_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_i_334_, v___x_343_);
lean_dec(v_i_334_);
v_i_334_ = v___x_344_;
v_source_335_ = v_source_341_;
v_target_336_ = v_target_342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3___redArg(lean_object* v_data_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_nbuckets_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_347_ = lean_array_get_size(v_data_346_);
v___x_348_ = lean_unsigned_to_nat(2u);
v_nbuckets_349_ = lean_nat_mul(v___x_347_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_box(0);
v___x_352_ = lean_mk_array(v_nbuckets_349_, v___x_351_);
v___x_353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10___redArg(v___x_350_, v_data_346_, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(lean_object* v_a_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
else
{
lean_object* v_key_357_; lean_object* v_tail_358_; size_t v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v_key_357_ = lean_ctor_get(v_x_355_, 0);
v_tail_358_ = lean_ctor_get(v_x_355_, 2);
v___x_359_ = lean_ptr_addr(v_key_357_);
v___x_360_ = lean_ptr_addr(v_a_354_);
v___x_361_ = lean_usize_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
v_x_355_ = v_tail_358_;
goto _start;
}
else
{
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg___boxed(lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_363_, v_x_364_);
lean_dec(v_x_364_);
lean_dec_ref(v_a_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4___redArg(lean_object* v_a_367_, lean_object* v_b_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_dec(v_b_368_);
lean_dec_ref(v_a_367_);
return v_x_369_;
}
else
{
lean_object* v_key_370_; lean_object* v_value_371_; lean_object* v_tail_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_386_; 
v_key_370_ = lean_ctor_get(v_x_369_, 0);
v_value_371_ = lean_ctor_get(v_x_369_, 1);
v_tail_372_ = lean_ctor_get(v_x_369_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_369_);
if (v_isSharedCheck_386_ == 0)
{
v___x_374_ = v_x_369_;
v_isShared_375_ = v_isSharedCheck_386_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_tail_372_);
lean_inc(v_value_371_);
lean_inc(v_key_370_);
lean_dec(v_x_369_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_386_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
size_t v___x_376_; size_t v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_ptr_addr(v_key_370_);
v___x_377_ = lean_ptr_addr(v_a_367_);
v___x_378_ = lean_usize_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4___redArg(v_a_367_, v_b_368_, v_tail_372_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 2, v___x_379_);
v___x_381_ = v___x_374_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_key_370_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_value_371_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_384_; 
lean_dec(v_value_371_);
lean_dec(v_key_370_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v_b_368_);
lean_ctor_set(v___x_374_, 0, v_a_367_);
v___x_384_ = v___x_374_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_b_368_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_tail_372_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(lean_object* v_m_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
lean_object* v_size_390_; lean_object* v_buckets_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_437_; 
v_size_390_ = lean_ctor_get(v_m_387_, 0);
v_buckets_391_ = lean_ctor_get(v_m_387_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_m_387_);
if (v_isSharedCheck_437_ == 0)
{
v___x_393_ = v_m_387_;
v_isShared_394_ = v_isSharedCheck_437_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_buckets_391_);
lean_inc(v_size_390_);
lean_dec(v_m_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_437_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v_fold_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v_bkt_411_; uint8_t v___x_412_; 
v___x_395_ = lean_array_get_size(v_buckets_391_);
v___x_396_ = lean_ptr_addr(v_a_388_);
v___x_397_ = ((size_t)3ULL);
v___x_398_ = lean_usize_shift_right(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_to_uint64(v___x_398_);
v___x_400_ = 32ULL;
v___x_401_ = lean_uint64_shift_right(v___x_399_, v___x_400_);
v_fold_402_ = lean_uint64_xor(v___x_399_, v___x_401_);
v___x_403_ = 16ULL;
v___x_404_ = lean_uint64_shift_right(v_fold_402_, v___x_403_);
v___x_405_ = lean_uint64_xor(v_fold_402_, v___x_404_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = lean_usize_of_nat(v___x_395_);
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_sub(v___x_407_, v___x_408_);
v___x_410_ = lean_usize_land(v___x_406_, v___x_409_);
v_bkt_411_ = lean_array_uget_borrowed(v_buckets_391_, v___x_410_);
v___x_412_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_388_, v_bkt_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v_size_x27_414_; lean_object* v___x_415_; lean_object* v_buckets_x27_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v_size_x27_414_ = lean_nat_add(v_size_390_, v___x_413_);
lean_dec(v_size_390_);
lean_inc(v_bkt_411_);
v___x_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_415_, 0, v_a_388_);
lean_ctor_set(v___x_415_, 1, v_b_389_);
lean_ctor_set(v___x_415_, 2, v_bkt_411_);
v_buckets_x27_416_ = lean_array_uset(v_buckets_391_, v___x_410_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(4u);
v___x_418_ = lean_nat_mul(v_size_x27_414_, v___x_417_);
v___x_419_ = lean_unsigned_to_nat(3u);
v___x_420_ = lean_nat_div(v___x_418_, v___x_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_array_get_size(v_buckets_x27_416_);
v___x_422_ = lean_nat_dec_le(v___x_420_, v___x_421_);
lean_dec(v___x_420_);
if (v___x_422_ == 0)
{
lean_object* v_val_423_; lean_object* v___x_425_; 
v_val_423_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3___redArg(v_buckets_x27_416_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_val_423_);
lean_ctor_set(v___x_393_, 0, v_size_x27_414_);
v___x_425_ = v___x_393_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_size_x27_414_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_val_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v___x_428_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_buckets_x27_416_);
lean_ctor_set(v___x_393_, 0, v_size_x27_414_);
v___x_428_ = v___x_393_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_size_x27_414_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_buckets_x27_416_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_object* v___x_430_; lean_object* v_buckets_x27_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_bkt_411_);
v___x_430_ = lean_box(0);
v_buckets_x27_431_ = lean_array_uset(v_buckets_391_, v___x_410_, v___x_430_);
v___x_432_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4___redArg(v_a_388_, v_b_389_, v_bkt_411_);
v___x_433_ = lean_array_uset(v_buckets_x27_431_, v___x_410_, v___x_432_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_433_);
v___x_435_ = v___x_393_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_size_390_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg(lean_object* v_e_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_Expr_hasMVar(v_e_438_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_e_438_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v_mctx_444_; lean_object* v___x_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_448_; lean_object* v_cache_449_; lean_object* v_zetaDeltaFVarIds_450_; lean_object* v_postponed_451_; lean_object* v_diag_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_461_; 
v___x_443_ = lean_st_ref_get(v___y_439_);
v_mctx_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_mctx_444_);
lean_dec(v___x_443_);
v___x_445_ = l_Lean_instantiateMVarsCore(v_mctx_444_, v_e_438_);
v_fst_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_fst_446_);
v_snd_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v___x_445_);
v___x_448_ = lean_st_ref_take(v___y_439_);
v_cache_449_ = lean_ctor_get(v___x_448_, 1);
v_zetaDeltaFVarIds_450_ = lean_ctor_get(v___x_448_, 2);
v_postponed_451_ = lean_ctor_get(v___x_448_, 3);
v_diag_452_ = lean_ctor_get(v___x_448_, 4);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_448_, 0);
lean_dec(v_unused_462_);
v___x_454_ = v___x_448_;
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_diag_452_);
lean_inc(v_postponed_451_);
lean_inc(v_zetaDeltaFVarIds_450_);
lean_inc(v_cache_449_);
lean_dec(v___x_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_snd_447_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_snd_447_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_cache_449_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_zetaDeltaFVarIds_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_postponed_451_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v_diag_452_);
v___x_457_ = v_reuseFailAlloc_460_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_st_ref_put(v___y_439_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_fst_446_);
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg___boxed(lean_object* v_e_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg(v_e_463_, v___y_464_);
lean_dec(v___y_464_);
return v_res_466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v_dummy_470_; 
v___x_469_ = lean_box(0);
v_dummy_470_ = l_Lean_Expr_sort___override(v___x_469_);
return v_dummy_470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(lean_object* v_upperBound_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v_modified_485_; 
v_modified_485_ = lean_nat_dec_lt(v_a_472_, v_upperBound_471_);
if (v_modified_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v_a_472_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_473_);
return v___x_486_;
}
else
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_519_; 
v_fst_487_ = lean_ctor_get(v_b_473_, 0);
v_snd_488_ = lean_ctor_get(v_b_473_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_b_473_);
if (v_isSharedCheck_519_ == 0)
{
v___x_490_ = v_b_473_;
v_isShared_491_ = v_isSharedCheck_519_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_b_473_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_519_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_array_fget_borrowed(v_snd_488_, v_a_472_);
lean_inc(v___x_492_);
v___x_493_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v___x_492_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_a_496_; size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_500_ = lean_ptr_addr(v___x_492_);
v___x_501_ = lean_ptr_addr(v_a_494_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec(v_fst_487_);
v___x_503_ = lean_array_fset(v_snd_488_, v_a_472_, v_a_494_);
v___x_504_ = lean_box(v_modified_485_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_503_);
lean_ctor_set(v___x_490_, 0, v___x_504_);
v___x_506_ = v___x_490_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_503_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_a_496_ = v___x_506_;
goto v___jp_495_;
}
}
else
{
lean_object* v___x_509_; 
lean_dec(v_a_494_);
if (v_isShared_491_ == 0)
{
v___x_509_ = v___x_490_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_488_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
v_a_496_ = v___x_509_;
goto v___jp_495_;
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_a_472_, v___x_497_);
lean_dec(v_a_472_);
v_a_472_ = v___x_498_;
v_b_473_ = v_a_496_;
goto _start;
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_490_);
lean_dec(v_snd_488_);
lean_dec(v_fst_487_);
lean_dec(v_a_472_);
v_a_511_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_493_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_493_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(lean_object* v_e_520_, uint8_t v_a_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
if (lean_obj_tag(v_x_522_) == 5)
{
lean_object* v_fn_536_; lean_object* v_arg_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_fn_536_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_fn_536_);
v_arg_537_ = lean_ctor_get(v_x_522_, 1);
lean_inc_ref(v_arg_537_);
lean_dec_ref_known(v_x_522_, 2);
v___x_538_ = lean_array_set(v_x_523_, v_x_524_, v_arg_537_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_sub(v_x_524_, v___x_539_);
lean_dec(v_x_524_);
v_x_522_ = v_fn_536_;
v_x_523_ = v___x_538_;
v_x_524_ = v___x_540_;
goto _start;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_x_524_);
v___x_542_ = lean_array_get_size(v_x_523_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_box(v_a_521_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_x_523_);
v___x_546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v___x_542_, v___x_543_, v___x_545_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_561_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_561_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_fst_551_; uint8_t v___x_552_; 
v_fst_551_ = lean_ctor_get(v_a_547_, 0);
v___x_552_ = lean_unbox(v_fst_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v_a_547_);
lean_dec_ref(v_x_522_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_e_520_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_e_520_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v_snd_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec_ref(v_e_520_);
v_snd_556_ = lean_ctor_get(v_a_547_, 1);
lean_inc(v_snd_556_);
lean_dec(v_a_547_);
v___x_557_ = l_Lean_mkAppN(v_x_522_, v_snd_556_);
lean_dec(v_snd_556_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_557_);
v___x_559_ = v___x_549_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_x_522_);
lean_dec_ref(v_e_520_);
v_a_562_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_546_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_546_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___lam__0(lean_object* v_fvars_570_, uint8_t v_modified_571_, lean_object* v_d_572_, lean_object* v_a_573_, lean_object* v_root_574_, lean_object* v_body_575_, lean_object* v_x_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_array_push(v_fvars_570_, v_x_576_);
if (v_modified_571_ == 0)
{
size_t v___x_589_; size_t v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_ptr_addr(v_d_572_);
v___x_590_ = lean_ptr_addr(v_a_573_);
v___x_591_ = lean_usize_dec_eq(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_592_ = 1;
v___x_593_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(v_root_574_, v_body_575_, v___x_588_, v___x_592_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(v_root_574_, v_body_575_, v___x_588_, v_modified_571_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_594_;
}
}
else
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(v_root_574_, v_body_575_, v___x_588_, v_modified_571_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___lam__0___boxed(lean_object** _args){
lean_object* v_fvars_596_ = _args[0];
lean_object* v_modified_597_ = _args[1];
lean_object* v_d_598_ = _args[2];
lean_object* v_a_599_ = _args[3];
lean_object* v_root_600_ = _args[4];
lean_object* v_body_601_ = _args[5];
lean_object* v_x_602_ = _args[6];
lean_object* v___y_603_ = _args[7];
lean_object* v___y_604_ = _args[8];
lean_object* v___y_605_ = _args[9];
lean_object* v___y_606_ = _args[10];
lean_object* v___y_607_ = _args[11];
lean_object* v___y_608_ = _args[12];
lean_object* v___y_609_ = _args[13];
lean_object* v___y_610_ = _args[14];
lean_object* v___y_611_ = _args[15];
lean_object* v___y_612_ = _args[16];
lean_object* v___y_613_ = _args[17];
_start:
{
uint8_t v_modified_boxed_614_; lean_object* v_res_615_; 
v_modified_boxed_614_ = lean_unbox(v_modified_597_);
v_res_615_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___lam__0(v_fvars_596_, v_modified_boxed_614_, v_d_598_, v_a_599_, v_root_600_, v_body_601_, v_x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v_a_599_);
lean_dec_ref(v_d_598_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(lean_object* v_root_616_, lean_object* v_e_617_, lean_object* v_fvars_618_, uint8_t v_modified_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
if (lean_obj_tag(v_e_617_) == 6)
{
lean_object* v_binderName_631_; lean_object* v_binderType_632_; lean_object* v_body_633_; uint8_t v_binderInfo_634_; lean_object* v_d_635_; lean_object* v___x_636_; 
v_binderName_631_ = lean_ctor_get(v_e_617_, 0);
lean_inc(v_binderName_631_);
v_binderType_632_ = lean_ctor_get(v_e_617_, 1);
lean_inc_ref(v_binderType_632_);
v_body_633_ = lean_ctor_get(v_e_617_, 2);
lean_inc_ref(v_body_633_);
v_binderInfo_634_ = lean_ctor_get_uint8(v_e_617_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_617_, 3);
v_d_635_ = lean_expr_instantiate_rev(v_binderType_632_, v_fvars_618_);
lean_dec_ref(v_binderType_632_);
lean_inc_ref(v_d_635_);
v___x_636_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_d_635_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v___f_639_; uint8_t v___x_640_; lean_object* v___x_641_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_n(v_a_637_, 2);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = lean_box(v_modified_619_);
v___f_639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___lam__0___boxed), 18, 6);
lean_closure_set(v___f_639_, 0, v_fvars_618_);
lean_closure_set(v___f_639_, 1, v___x_638_);
lean_closure_set(v___f_639_, 2, v_d_635_);
lean_closure_set(v___f_639_, 3, v_a_637_);
lean_closure_set(v___f_639_, 4, v_root_616_);
lean_closure_set(v___f_639_, 5, v_body_633_);
v___x_640_ = 0;
v___x_641_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg(v_binderName_631_, v_binderInfo_634_, v_a_637_, v___f_639_, v___x_640_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_641_;
}
else
{
lean_dec_ref(v_d_635_);
lean_dec_ref(v_body_633_);
lean_dec(v_binderName_631_);
lean_dec_ref(v_fvars_618_);
lean_dec_ref(v_root_616_);
return v___x_636_;
}
}
else
{
lean_object* v_e_642_; lean_object* v___x_643_; 
v_e_642_ = lean_expr_instantiate_rev(v_e_617_, v_fvars_618_);
lean_dec_ref(v_e_617_);
lean_inc_ref(v_e_642_);
v___x_643_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_642_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_659_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_659_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
if (v_modified_619_ == 0)
{
size_t v___x_653_; size_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_ptr_addr(v_e_642_);
lean_dec_ref(v_e_642_);
v___x_654_ = lean_ptr_addr(v_a_644_);
v___x_655_ = lean_usize_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_del_object(v___x_646_);
lean_dec_ref(v_root_616_);
goto v___jp_648_;
}
else
{
lean_object* v___x_657_; 
lean_dec(v_a_644_);
lean_dec_ref(v_fvars_618_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v_root_616_);
v___x_657_ = v___x_646_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_root_616_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_del_object(v___x_646_);
lean_dec_ref(v_e_642_);
lean_dec_ref(v_root_616_);
goto v___jp_648_;
}
v___jp_648_:
{
uint8_t v___x_649_; uint8_t v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; 
v___x_649_ = 1;
v___x_650_ = 0;
v___x_651_ = 1;
v___x_652_ = l_Lean_Meta_mkLambdaFVars(v_fvars_618_, v_a_644_, v___x_650_, v___x_649_, v___x_650_, v___x_649_, v___x_651_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec_ref(v_fvars_618_);
return v___x_652_;
}
}
}
else
{
lean_dec_ref(v_e_642_);
lean_dec_ref(v_fvars_618_);
lean_dec_ref(v_root_616_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda(lean_object* v_root_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___closed__0));
v___x_673_ = 0;
lean_inc_ref(v_root_660_);
v___x_674_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(v_root_660_, v_root_660_, v___x_672_, v___x_673_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3));
v___x_679_ = lean_unsigned_to_nat(13u);
v___x_680_ = lean_unsigned_to_nat(92u);
v___x_681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2));
v___x_682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1));
v___x_683_ = l_mkPanicMessageWithDecl(v___x_682_, v___x_681_, v___x_680_, v___x_679_, v___x_678_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg(v_e_684_, v_a_692_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l_Lean_Core_betaReduce(v_a_697_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = l_Lean_Meta_Sym_unfoldReducible(v_a_699_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_a_701_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_703_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = l_Lean_Meta_Grind_foldProjs(v_a_705_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Meta_Sym_normalizeLevels(v_a_707_, v_a_693_, v_a_694_);
return v___x_708_;
}
else
{
return v___x_706_;
}
}
else
{
return v___x_704_;
}
}
else
{
return v___x_702_;
}
}
else
{
return v___x_700_;
}
}
else
{
return v___x_698_;
}
}
else
{
return v___x_696_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_box(0);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5));
v___x_711_ = l_Lean_mkConst(v___x_710_, v___x_709_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
v___x_713_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3));
v___x_714_ = l_Lean_mkConst(v___x_713_, v___x_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(lean_object* v_e_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_e_x27_728_; lean_object* v___y_729_; uint8_t v___x_734_; 
v___x_734_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_715_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_st_ref_get(v_a_716_);
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v___x_735_, v_e_715_);
lean_dec(v___x_735_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v_e_715_);
v_val_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 0);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v___x_745_; 
lean_dec(v___x_736_);
lean_inc(v_a_725_);
lean_inc_ref(v_a_724_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc_ref(v_e_715_);
v___x_745_ = lean_infer_type(v_e_715_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_n(v_a_746_, 2);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = l_Lean_Meta_isProp(v_a_746_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; uint8_t v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = lean_unbox(v_a_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(v_a_746_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_811_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_811_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_811_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_811_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
if (lean_obj_tag(v_a_751_) == 1)
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_del_object(v___x_753_);
lean_dec(v_a_748_);
v_val_788_ = lean_ctor_get(v_a_751_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_a_751_, 1);
v___x_789_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_val_788_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_802_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_802_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_794_ = lean_st_ref_take(v_a_716_);
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5);
lean_inc_ref(v_e_715_);
v___x_796_ = l_Lean_mkAppB(v___x_795_, v_a_790_, v_e_715_);
lean_inc_ref(v___x_796_);
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_794_, v_e_715_, v___x_796_);
v___x_798_ = lean_st_ref_put(v_a_716_, v___x_797_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_796_);
v___x_800_ = v___x_792_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_796_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_dec_ref(v_e_715_);
return v___x_789_;
}
}
else
{
uint8_t v___x_803_; 
lean_dec(v_a_751_);
v___x_803_ = l_Lean_Expr_isApp(v_e_715_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = l_Lean_Expr_isForall(v_e_715_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
v___x_805_ = l_Lean_Expr_isLambda(v_e_715_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_Expr_isProj(v_e_715_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_Expr_isMData(v_e_715_);
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_a_748_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_e_715_);
v___x_809_ = v___x_753_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_e_715_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_del_object(v___x_753_);
goto v___jp_755_;
}
}
else
{
lean_del_object(v___x_753_);
goto v___jp_755_;
}
}
else
{
lean_del_object(v___x_753_);
goto v___jp_755_;
}
}
else
{
lean_del_object(v___x_753_);
goto v___jp_755_;
}
}
else
{
lean_del_object(v___x_753_);
goto v___jp_755_;
}
}
v___jp_755_:
{
switch(lean_obj_tag(v_e_715_))
{
case 5:
{
lean_object* v_dummy_756_; lean_object* v_nargs_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; 
v_dummy_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0);
v_nargs_757_ = l_Lean_Expr_getAppNumArgs(v_e_715_);
lean_inc(v_nargs_757_);
v___x_758_ = lean_mk_array(v_nargs_757_, v_dummy_756_);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_sub(v_nargs_757_, v___x_759_);
lean_dec(v_nargs_757_);
v___x_761_ = lean_unbox(v_a_748_);
lean_dec(v_a_748_);
lean_inc_ref_n(v_e_715_, 2);
v___x_762_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(v_e_715_, v___x_761_, v_e_715_, v___x_758_, v___x_760_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_e_x27_728_ = v_a_763_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
else
{
lean_dec_ref_known(v_e_715_, 2);
return v___x_762_;
}
}
case 11:
{
lean_object* v_typeName_764_; lean_object* v_idx_765_; lean_object* v_struct_766_; lean_object* v___x_767_; 
lean_dec(v_a_748_);
v_typeName_764_ = lean_ctor_get(v_e_715_, 0);
v_idx_765_ = lean_ctor_get(v_e_715_, 1);
v_struct_766_ = lean_ctor_get(v_e_715_, 2);
lean_inc_ref(v_struct_766_);
v___x_767_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_struct_766_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; size_t v___x_769_; size_t v___x_770_; uint8_t v___x_771_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = lean_ptr_addr(v_struct_766_);
v___x_770_ = lean_ptr_addr(v_a_768_);
v___x_771_ = lean_usize_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_inc(v_idx_765_);
lean_inc(v_typeName_764_);
v___x_772_ = l_Lean_Expr_proj___override(v_typeName_764_, v_idx_765_, v_a_768_);
v_e_x27_728_ = v___x_772_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
else
{
lean_dec(v_a_768_);
lean_inc_ref(v_e_715_);
v_e_x27_728_ = v_e_715_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
}
else
{
lean_dec_ref_known(v_e_715_, 3);
return v___x_767_;
}
}
case 10:
{
lean_object* v_data_773_; lean_object* v_expr_774_; lean_object* v___x_775_; 
lean_dec(v_a_748_);
v_data_773_ = lean_ctor_get(v_e_715_, 0);
v_expr_774_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_expr_774_);
v___x_775_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_expr_774_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; size_t v___x_777_; size_t v___x_778_; uint8_t v___x_779_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = lean_ptr_addr(v_expr_774_);
v___x_778_ = lean_ptr_addr(v_a_776_);
v___x_779_ = lean_usize_dec_eq(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_inc(v_data_773_);
v___x_780_ = l_Lean_Expr_mdata___override(v_data_773_, v_a_776_);
v_e_x27_728_ = v___x_780_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
else
{
lean_dec(v_a_776_);
lean_inc_ref(v_e_715_);
v_e_x27_728_ = v_e_715_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
}
else
{
lean_dec_ref_known(v_e_715_, 2);
return v___x_775_;
}
}
case 7:
{
lean_object* v___x_781_; 
lean_dec(v_a_748_);
lean_inc_ref(v_e_715_);
v___x_781_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall(v_e_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v_e_x27_728_ = v_a_782_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
else
{
lean_dec_ref_known(v_e_715_, 3);
return v___x_781_;
}
}
case 6:
{
lean_object* v___x_783_; 
lean_dec(v_a_748_);
lean_inc_ref(v_e_715_);
v___x_783_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda(v_e_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v_e_x27_728_ = v_a_784_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
else
{
lean_dec_ref_known(v_e_715_, 3);
return v___x_783_;
}
}
default: 
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_a_748_);
v___x_785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4);
v___x_786_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(v___x_785_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v_e_x27_728_ = v_a_787_;
v___y_729_ = v_a_716_;
goto v___jp_727_;
}
else
{
lean_dec_ref(v_e_715_);
return v___x_786_;
}
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_a_748_);
lean_dec_ref(v_e_715_);
v_a_812_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_750_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_750_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
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
else
{
lean_object* v___x_820_; 
lean_dec(v_a_748_);
v___x_820_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_a_746_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_833_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_833_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_825_ = lean_st_ref_take(v_a_716_);
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6);
lean_inc_ref(v_e_715_);
v___x_827_ = l_Lean_mkAppB(v___x_826_, v_a_821_, v_e_715_);
lean_inc_ref(v___x_827_);
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_825_, v_e_715_, v___x_827_);
v___x_829_ = lean_st_ref_put(v_a_716_, v___x_828_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_831_ = v___x_823_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_827_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_dec_ref(v_e_715_);
return v___x_820_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_746_);
lean_dec_ref(v_e_715_);
v_a_834_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_747_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_747_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_dec_ref(v_e_715_);
return v___x_745_;
}
}
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v_e_715_);
return v___x_842_;
}
v___jp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_730_ = lean_st_ref_take(v___y_729_);
lean_inc_ref(v_e_x27_728_);
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_730_, v_e_715_, v_e_x27_728_);
v___x_732_ = lean_st_ref_put(v___y_729_, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_e_x27_728_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___lam__0(lean_object* v_fvars_843_, uint8_t v_modified_844_, lean_object* v_d_845_, lean_object* v_a_846_, lean_object* v_root_847_, lean_object* v_body_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_array_push(v_fvars_843_, v_x_849_);
if (v_modified_844_ == 0)
{
size_t v___x_862_; size_t v___x_863_; uint8_t v___x_864_; 
v___x_862_ = lean_ptr_addr(v_d_845_);
v___x_863_ = lean_ptr_addr(v_a_846_);
v___x_864_ = lean_usize_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; lean_object* v___x_866_; 
v___x_865_ = 1;
v___x_866_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(v_root_847_, v_body_848_, v___x_861_, v___x_865_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(v_root_847_, v_body_848_, v___x_861_, v_modified_844_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_867_;
}
}
else
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(v_root_847_, v_body_848_, v___x_861_, v_modified_844_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___lam__0___boxed(lean_object** _args){
lean_object* v_fvars_869_ = _args[0];
lean_object* v_modified_870_ = _args[1];
lean_object* v_d_871_ = _args[2];
lean_object* v_a_872_ = _args[3];
lean_object* v_root_873_ = _args[4];
lean_object* v_body_874_ = _args[5];
lean_object* v_x_875_ = _args[6];
lean_object* v___y_876_ = _args[7];
lean_object* v___y_877_ = _args[8];
lean_object* v___y_878_ = _args[9];
lean_object* v___y_879_ = _args[10];
lean_object* v___y_880_ = _args[11];
lean_object* v___y_881_ = _args[12];
lean_object* v___y_882_ = _args[13];
lean_object* v___y_883_ = _args[14];
lean_object* v___y_884_ = _args[15];
lean_object* v___y_885_ = _args[16];
lean_object* v___y_886_ = _args[17];
_start:
{
uint8_t v_modified_boxed_887_; lean_object* v_res_888_; 
v_modified_boxed_887_ = lean_unbox(v_modified_870_);
v_res_888_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___lam__0(v_fvars_869_, v_modified_boxed_887_, v_d_871_, v_a_872_, v_root_873_, v_body_874_, v_x_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v_a_872_);
lean_dec_ref(v_d_871_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(lean_object* v_root_889_, lean_object* v_e_890_, lean_object* v_fvars_891_, uint8_t v_modified_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_e_890_) == 7)
{
lean_object* v_binderName_904_; lean_object* v_binderType_905_; lean_object* v_body_906_; uint8_t v_binderInfo_907_; lean_object* v_d_908_; lean_object* v___x_909_; 
v_binderName_904_ = lean_ctor_get(v_e_890_, 0);
lean_inc(v_binderName_904_);
v_binderType_905_ = lean_ctor_get(v_e_890_, 1);
lean_inc_ref(v_binderType_905_);
v_body_906_ = lean_ctor_get(v_e_890_, 2);
lean_inc_ref(v_body_906_);
v_binderInfo_907_ = lean_ctor_get_uint8(v_e_890_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_890_, 3);
v_d_908_ = lean_expr_instantiate_rev(v_binderType_905_, v_fvars_891_);
lean_dec_ref(v_binderType_905_);
lean_inc_ref(v_d_908_);
v___x_909_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_d_908_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___f_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_n(v_a_910_, 2);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = lean_box(v_modified_892_);
v___f_912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___lam__0___boxed), 18, 6);
lean_closure_set(v___f_912_, 0, v_fvars_891_);
lean_closure_set(v___f_912_, 1, v___x_911_);
lean_closure_set(v___f_912_, 2, v_d_908_);
lean_closure_set(v___f_912_, 3, v_a_910_);
lean_closure_set(v___f_912_, 4, v_root_889_);
lean_closure_set(v___f_912_, 5, v_body_906_);
v___x_913_ = 0;
v___x_914_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg(v_binderName_904_, v_binderInfo_907_, v_a_910_, v___f_912_, v___x_913_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_914_;
}
else
{
lean_dec_ref(v_d_908_);
lean_dec_ref(v_body_906_);
lean_dec(v_binderName_904_);
lean_dec_ref(v_fvars_891_);
lean_dec_ref(v_root_889_);
return v___x_909_;
}
}
else
{
lean_object* v_e_915_; lean_object* v___x_916_; 
v_e_915_ = lean_expr_instantiate_rev(v_e_890_, v_fvars_891_);
lean_dec_ref(v_e_890_);
lean_inc_ref(v_e_915_);
v___x_916_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_915_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_932_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_932_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
if (v_modified_892_ == 0)
{
size_t v___x_926_; size_t v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_ptr_addr(v_e_915_);
lean_dec_ref(v_e_915_);
v___x_927_ = lean_ptr_addr(v_a_917_);
v___x_928_ = lean_usize_dec_eq(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_del_object(v___x_919_);
lean_dec_ref(v_root_889_);
goto v___jp_921_;
}
else
{
lean_object* v___x_930_; 
lean_dec(v_a_917_);
lean_dec_ref(v_fvars_891_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_root_889_);
v___x_930_ = v___x_919_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_root_889_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_del_object(v___x_919_);
lean_dec_ref(v_e_915_);
lean_dec_ref(v_root_889_);
goto v___jp_921_;
}
v___jp_921_:
{
uint8_t v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_922_ = 1;
v___x_923_ = 0;
v___x_924_ = 1;
v___x_925_ = l_Lean_Meta_mkForallFVars(v_fvars_891_, v_a_917_, v___x_923_, v___x_922_, v___x_922_, v___x_924_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec_ref(v_fvars_891_);
return v___x_925_;
}
}
}
else
{
lean_dec_ref(v_e_915_);
lean_dec_ref(v_fvars_891_);
lean_dec_ref(v_root_889_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall(lean_object* v_root_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; 
v___x_945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___closed__0));
v___x_946_ = 0;
lean_inc_ref(v_root_933_);
v___x_947_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(v_root_933_, v_root_933_, v___x_945_, v___x_946_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall___boxed(lean_object* v_root_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall(v_root_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec(v_a_949_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda___boxed(lean_object* v_root_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda(v_root_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec(v_a_962_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3___boxed(lean_object* v_e_974_, lean_object* v_a_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v_a_77143__boxed_990_; lean_object* v_res_991_; 
v_a_77143__boxed_990_ = lean_unbox(v_a_975_);
v_res_991_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(v_e_974_, v_a_77143__boxed_990_, v_x_976_, v_x_977_, v_x_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess___boxed(lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec(v_a_993_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg___boxed(lean_object* v_upperBound_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v_upperBound_1005_, v_a_1006_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec(v_upperBound_1005_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop___boxed(lean_object* v_root_1020_, lean_object* v_e_1021_, lean_object* v_fvars_1022_, lean_object* v_modified_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
uint8_t v_modified_boxed_1035_; lean_object* v_res_1036_; 
v_modified_boxed_1035_ = lean_unbox(v_modified_1023_);
v_res_1036_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitForall_loop(v_root_1020_, v_e_1021_, v_fvars_1022_, v_modified_boxed_1035_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec(v_a_1024_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop___boxed(lean_object* v_root_1037_, lean_object* v_e_1038_, lean_object* v_fvars_1039_, lean_object* v_modified_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
uint8_t v_modified_boxed_1052_; lean_object* v_res_1053_; 
v_modified_boxed_1052_ = lean_unbox(v_modified_1040_);
v_res_1053_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop(v_root_1037_, v_e_1038_, v_fvars_1039_, v_modified_boxed_1052_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec(v_a_1041_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___boxed(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec(v_a_1055_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7(lean_object* v_00_u03b1_1067_, lean_object* v_name_1068_, uint8_t v_bi_1069_, lean_object* v_type_1070_, lean_object* v_k_1071_, uint8_t v_kind_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___redArg(v_name_1068_, v_bi_1069_, v_type_1070_, v_k_1071_, v_kind_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_1085_ = _args[0];
lean_object* v_name_1086_ = _args[1];
lean_object* v_bi_1087_ = _args[2];
lean_object* v_type_1088_ = _args[3];
lean_object* v_k_1089_ = _args[4];
lean_object* v_kind_1090_ = _args[5];
lean_object* v___y_1091_ = _args[6];
lean_object* v___y_1092_ = _args[7];
lean_object* v___y_1093_ = _args[8];
lean_object* v___y_1094_ = _args[9];
lean_object* v___y_1095_ = _args[10];
lean_object* v___y_1096_ = _args[11];
lean_object* v___y_1097_ = _args[12];
lean_object* v___y_1098_ = _args[13];
lean_object* v___y_1099_ = _args[14];
lean_object* v___y_1100_ = _args[15];
lean_object* v___y_1101_ = _args[16];
_start:
{
uint8_t v_bi_boxed_1102_; uint8_t v_kind_boxed_1103_; lean_object* v_res_1104_; 
v_bi_boxed_1102_ = lean_unbox(v_bi_1087_);
v_kind_boxed_1103_ = lean_unbox(v_kind_1090_);
v_res_1104_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visitLambda_loop_spec__7(v_00_u03b1_1085_, v_name_1086_, v_bi_boxed_1102_, v_type_1088_, v_k_1089_, v_kind_boxed_1103_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v___y_1091_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11(lean_object* v_e_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___redArg(v_e_1105_, v___y_1113_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11___boxed(lean_object* v_e_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__11(v_e_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0(lean_object* v_00_u03b2_1131_, lean_object* v_m_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v_m_1132_, v_a_1133_, v_b_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(lean_object* v_00_u03b2_1136_, lean_object* v_m_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v_m_1137_, v_a_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___boxed(lean_object* v_00_u03b2_1140_, lean_object* v_m_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(v_00_u03b2_1140_, v_m_1141_, v_a_1142_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_m_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(lean_object* v_upperBound_1144_, lean_object* v___x_1145_, lean_object* v_inst_1146_, lean_object* v_R_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v_c_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v_upperBound_1144_, v_a_1148_, v_b_1149_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_1163_ = _args[0];
lean_object* v___x_1164_ = _args[1];
lean_object* v_inst_1165_ = _args[2];
lean_object* v_R_1166_ = _args[3];
lean_object* v_a_1167_ = _args[4];
lean_object* v_b_1168_ = _args[5];
lean_object* v_c_1169_ = _args[6];
lean_object* v___y_1170_ = _args[7];
lean_object* v___y_1171_ = _args[8];
lean_object* v___y_1172_ = _args[9];
lean_object* v___y_1173_ = _args[10];
lean_object* v___y_1174_ = _args[11];
lean_object* v___y_1175_ = _args[12];
lean_object* v___y_1176_ = _args[13];
lean_object* v___y_1177_ = _args[14];
lean_object* v___y_1178_ = _args[15];
lean_object* v___y_1179_ = _args[16];
lean_object* v___y_1180_ = _args[17];
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(v_upperBound_1163_, v___x_1164_, v_inst_1165_, v_R_1166_, v_a_1167_, v_b_1168_, v_c_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec(v___x_1164_);
lean_dec(v_upperBound_1163_);
return v_res_1181_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2(lean_object* v_00_u03b2_1182_, lean_object* v_a_1183_, lean_object* v_x_1184_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_1183_, v_x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1186_, lean_object* v_a_1187_, lean_object* v_x_1188_){
_start:
{
uint8_t v_res_1189_; lean_object* v_r_1190_; 
v_res_1189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2(v_00_u03b2_1186_, v_a_1187_, v_x_1188_);
lean_dec(v_x_1188_);
lean_dec_ref(v_a_1187_);
v_r_1190_ = lean_box(v_res_1189_);
return v_r_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3(lean_object* v_00_u03b2_1191_, lean_object* v_data_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3___redArg(v_data_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4(lean_object* v_00_u03b2_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__4___redArg(v_a_1195_, v_b_1196_, v_x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6(lean_object* v_00_u03b2_1199_, lean_object* v_a_1200_, lean_object* v_x_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___redArg(v_a_1200_, v_x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1203_, lean_object* v_a_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__6(v_00_u03b2_1203_, v_a_1204_, v_x_1205_);
lean_dec(v_x_1205_);
lean_dec_ref(v_a_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1207_, lean_object* v_i_1208_, lean_object* v_source_1209_, lean_object* v_target_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10___redArg(v_i_1208_, v_source_1209_, v_target_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10_spec__14(lean_object* v_00_u03b2_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__3_spec__10_spec__14___redArg(v_x_1213_, v_x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(lean_object* v_category_1216_, lean_object* v_opts_1217_, lean_object* v_act_1218_, lean_object* v_decl_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1227_);
lean_inc(v___y_1226_);
lean_inc_ref(v___y_1225_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
v___x_1230_ = lean_apply_9(v_act_1218_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
v___x_1231_ = l_Lean_profileitIOUnsafe___redArg(v_category_1216_, v_opts_1217_, v___x_1230_, v_decl_1219_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg___boxed(lean_object* v_category_1232_, lean_object* v_opts_1233_, lean_object* v_act_1234_, lean_object* v_decl_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(v_category_1232_, v_opts_1233_, v_act_1234_, v_decl_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v_opts_1233_);
lean_dec_ref(v_category_1232_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(lean_object* v_00_u03b1_1247_, lean_object* v_category_1248_, lean_object* v_opts_1249_, lean_object* v_act_1250_, lean_object* v_decl_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(v_category_1248_, v_opts_1249_, v_act_1250_, v_decl_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_category_1264_, lean_object* v_opts_1265_, lean_object* v_act_1266_, lean_object* v_decl_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(v_00_u03b1_1263_, v_category_1264_, v_opts_1265_, v_act_1266_, v_decl_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v_opts_1265_);
lean_dec_ref(v_category_1264_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(lean_object* v___x_1279_, lean_object* v_e_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_st_mk_ref(v___x_1279_);
v___x_1292_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_1280_, v___x_1291_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_st_ref_get(v___x_1291_);
lean_dec(v___x_1291_);
lean_dec(v___x_1297_);
if (v_isShared_1296_ == 0)
{
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1293_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_dec(v___x_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed(lean_object* v___x_1302_, lean_object* v_e_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(v___x_1302_, v_e_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_unsigned_to_nat(16u);
v___x_1318_ = lean_mk_array(v___x_1317_, v___x_1316_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_obj_once(&l_Lean_Meta_Grind_markNestedSubsingletons___closed__1, &l_Lean_Meta_Grind_markNestedSubsingletons___closed__1_once, _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__1);
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v___x_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object* v_e_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_options_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_options_1333_ = lean_ctor_get(v_a_1330_, 2);
v___x_1334_ = ((lean_object*)(l_Lean_Meta_Grind_markNestedSubsingletons___closed__0));
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Grind_markNestedSubsingletons___closed__2, &l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once, _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2);
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1336_, 0, v___x_1335_);
lean_closure_set(v___f_1336_, 1, v_e_1322_);
v___x_1337_ = lean_box(0);
v___x_1338_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(v___x_1334_, v_options_1333_, v___f_1336_, v___x_1337_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___boxed(lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_e_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1363_; 
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
lean_inc(v_a_1359_);
lean_inc_ref(v_a_1358_);
lean_inc_ref(v_e_1351_);
v___x_1363_ = lean_infer_type(v_e_1351_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_a_1364_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1375_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6);
v___x_1371_ = l_Lean_mkAppB(v___x_1370_, v_a_1366_, v_e_1351_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1371_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_dec_ref(v_e_1351_);
return v___x_1365_;
}
}
else
{
lean_dec_ref(v_e_1351_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof___boxed(lean_object* v_e_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(v_e_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec(v_a_1377_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof(lean_object* v_e_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3));
v___x_1401_ = l_Lean_Expr_isAppOf(v_e_1389_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_obj_once(&l_Lean_Meta_Grind_markNestedSubsingletons___closed__2, &l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once, _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2);
v___x_1403_ = lean_st_mk_ref(v___x_1402_);
v___x_1404_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(v_e_1389_, v___x_1403_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = lean_st_ref_get(v___x_1403_);
lean_dec(v___x_1403_);
lean_dec(v___x_1409_);
if (v_isShared_1408_ == 0)
{
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1405_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_dec(v___x_1403_);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_e_1389_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof___boxed(lean_object* v_e_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Meta_Grind_markProof(v_e_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
return v_res_1426_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
}
#ifdef __cplusplus
}
#endif
