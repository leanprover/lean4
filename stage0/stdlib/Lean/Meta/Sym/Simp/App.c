// Lean compiler output
// Module: Lean.Meta.Sym.Simp.App
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Tactic.Simp.Types import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.CongrInfo import Init.Omega
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congrFun'"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 239, 156, 219, 118, 185, 235, 192)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to build congruence proof, function expected"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.Simp.App"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpOverApplied.visit"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.propagateOverApplied.visit"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "function type expected"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.getFnType"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpFixedPrefix.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpInterlaced.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpUsingCongrThm.simpEqArgs"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpUsingCongrThm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0;
static const lean_array_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpAppArgRange.visit"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Sym.Simp.simpAppArgRange"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "assertion violation: start < stop\n  "};
static const lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*7);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec_ref(v___y_3_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
lean_inc_ref(v_f_1_);
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v___x_16_);
lean_inc(v___y_4_);
lean_inc_ref(v_a_2_);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref(v___x_17_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec(v___y_4_);
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec(v___y_4_);
lean_dec_ref(v___y_3_);
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_26_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_16_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_16_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_app___override(v_f_1_, v_a_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
lean_dec(v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object* v_f_34_, lean_object* v_a_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_34_, v_a_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object* v_a_44_, lean_object* v_e_45_, lean_object* v_declName_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; 
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
v___x_54_ = l_Lean_Meta_Sym_inferType___redArg(v_a_44_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_55_);
lean_dec_ref(v___x_54_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
lean_inc(v_a_55_);
v___x_56_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_55_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
lean_dec_ref(v___x_56_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
v___x_58_ = l_Lean_Meta_Sym_inferType___redArg(v_e_45_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
lean_dec_ref(v___x_58_);
lean_inc(v_a_59_);
v___x_60_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_59_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_73_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_73_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v_a_61_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_67_, 0, v_a_57_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = l_Lean_mkConst(v_declName_46_, v___x_67_);
v___x_69_ = l_Lean_mkAppB(v___x_68_, v_a_55_, v_a_59_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_69_);
v___x_71_ = v___x_63_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
lean_dec(v_a_59_);
lean_dec(v_a_57_);
lean_dec(v_a_55_);
lean_dec(v_declName_46_);
v_a_74_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_60_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_60_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_dec(v_a_57_);
lean_dec(v_a_55_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v_declName_46_);
return v___x_58_;
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec(v_a_55_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v_declName_46_);
lean_dec_ref(v_e_45_);
v_a_82_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_56_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_56_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v_declName_46_);
lean_dec_ref(v_e_45_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object* v_a_90_, lean_object* v_e_91_, lean_object* v_declName_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_90_, v_e_91_, v_declName_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object* v_e_112_, lean_object* v_f_113_, lean_object* v_a_114_, lean_object* v_fr_115_, lean_object* v_ar_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
if (lean_obj_tag(v_fr_115_) == 0)
{
lean_dec_ref(v_fr_115_);
if (lean_obj_tag(v_ar_116_) == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec_ref(v_ar_116_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v___x_124_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v_e_x27_126_; lean_object* v_proof_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_164_; 
v_e_x27_126_ = lean_ctor_get(v_ar_116_, 0);
v_proof_127_ = lean_ctor_get(v_ar_116_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_ar_116_);
if (v_isSharedCheck_164_ == 0)
{
v___x_129_ = v_ar_116_;
v_isShared_130_ = v_isSharedCheck_164_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_proof_127_);
lean_inc(v_e_x27_126_);
lean_dec(v_ar_116_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_164_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; 
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc_ref(v_e_x27_126_);
lean_inc_ref(v_f_113_);
v___x_131_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_113_, v_e_x27_126_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
v___x_133_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
lean_inc_ref(v_a_114_);
v___x_134_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_114_, v_e_112_, v___x_133_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_147_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_147_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_142_; 
v___x_139_ = l_Lean_mkApp4(v_a_135_, v_a_114_, v_e_x27_126_, v_f_113_, v_proof_127_);
v___x_140_ = 0;
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_139_);
lean_ctor_set(v___x_129_, 0, v_a_132_);
v___x_142_ = v___x_129_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_139_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*2, v___x_140_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_142_);
v___x_144_ = v___x_137_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
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
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_a_132_);
lean_del_object(v___x_129_);
lean_dec_ref(v_proof_127_);
lean_dec_ref(v_e_x27_126_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
v_a_148_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_134_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_134_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_del_object(v___x_129_);
lean_dec_ref(v_proof_127_);
lean_dec_ref(v_e_x27_126_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_a_156_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_131_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_131_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_ar_116_) == 0)
{
lean_object* v_e_x27_165_; lean_object* v_proof_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v_ar_116_);
v_e_x27_165_ = lean_ctor_get(v_fr_115_, 0);
v_proof_166_ = lean_ctor_get(v_fr_115_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_fr_115_);
if (v_isSharedCheck_203_ == 0)
{
v___x_168_ = v_fr_115_;
v_isShared_169_ = v_isSharedCheck_203_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_proof_166_);
lean_inc(v_e_x27_165_);
lean_dec(v_fr_115_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_203_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; 
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc_ref(v_a_114_);
lean_inc_ref(v_e_x27_165_);
v___x_170_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_165_, v_a_114_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
lean_inc_ref(v_a_114_);
v___x_173_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_114_, v_e_112_, v___x_172_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_186_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_186_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; uint8_t v___x_179_; lean_object* v___x_181_; 
v___x_178_ = l_Lean_mkApp4(v_a_174_, v_f_113_, v_e_x27_165_, v_proof_166_, v_a_114_);
v___x_179_ = 0;
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_178_);
lean_ctor_set(v___x_168_, 0, v_a_171_);
v___x_181_ = v___x_168_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_171_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_178_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*2, v___x_179_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_181_);
v___x_183_ = v___x_176_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec(v_a_171_);
lean_del_object(v___x_168_);
lean_dec_ref(v_proof_166_);
lean_dec_ref(v_e_x27_165_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
v_a_187_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_173_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_173_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_del_object(v___x_168_);
lean_dec_ref(v_proof_166_);
lean_dec_ref(v_e_x27_165_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_a_195_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_170_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_170_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_e_x27_204_; lean_object* v_proof_205_; lean_object* v_e_x27_206_; lean_object* v_proof_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_244_; 
v_e_x27_204_ = lean_ctor_get(v_fr_115_, 0);
lean_inc_ref(v_e_x27_204_);
v_proof_205_ = lean_ctor_get(v_fr_115_, 1);
lean_inc_ref(v_proof_205_);
lean_dec_ref(v_fr_115_);
v_e_x27_206_ = lean_ctor_get(v_ar_116_, 0);
v_proof_207_ = lean_ctor_get(v_ar_116_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_ar_116_);
if (v_isSharedCheck_244_ == 0)
{
v___x_209_ = v_ar_116_;
v_isShared_210_ = v_isSharedCheck_244_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_proof_207_);
lean_inc(v_e_x27_206_);
lean_dec(v_ar_116_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_244_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; 
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc_ref(v_e_x27_206_);
lean_inc_ref(v_e_x27_204_);
v___x_211_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_204_, v_e_x27_206_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
v___x_213_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
lean_inc_ref(v_a_114_);
v___x_214_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_114_, v_e_112_, v___x_213_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_227_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_227_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_227_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_227_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_222_; 
v___x_219_ = l_Lean_mkApp6(v_a_215_, v_f_113_, v_e_x27_204_, v_a_114_, v_e_x27_206_, v_proof_205_, v_proof_207_);
v___x_220_ = 0;
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_219_);
lean_ctor_set(v___x_209_, 0, v_a_212_);
v___x_222_ = v___x_209_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_212_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_219_);
v___x_222_ = v_reuseFailAlloc_226_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; 
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*2, v___x_220_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_222_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_212_);
lean_del_object(v___x_209_);
lean_dec_ref(v_proof_207_);
lean_dec_ref(v_e_x27_206_);
lean_dec_ref(v_proof_205_);
lean_dec_ref(v_e_x27_204_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
v_a_228_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_214_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_214_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_del_object(v___x_209_);
lean_dec_ref(v_proof_207_);
lean_dec_ref(v_e_x27_206_);
lean_dec_ref(v_proof_205_);
lean_dec_ref(v_e_x27_204_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_a_236_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_211_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_211_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object* v_e_245_, lean_object* v_f_246_, lean_object* v_a_247_, lean_object* v_fr_248_, lean_object* v_ar_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_245_, v_f_246_, v_a_247_, v_fr_248_, v_ar_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object* v_e_258_, lean_object* v_f_259_, lean_object* v_a_260_, lean_object* v_fr_261_, lean_object* v_ar_262_, lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_258_, v_f_259_, v_a_260_, v_fr_261_, v_ar_262_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object* v_e_272_, lean_object* v_f_273_, lean_object* v_a_274_, lean_object* v_fr_275_, lean_object* v_ar_276_, lean_object* v_x_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Meta_Sym_Simp_mkCongr(v_e_272_, v_f_273_, v_a_274_, v_fr_275_, v_ar_276_, v_x_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; lean_object* v_env_293_; lean_object* v___x_294_; lean_object* v_mctx_295_; lean_object* v_lctx_296_; lean_object* v_options_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_292_ = lean_st_ref_get(v___y_290_);
v_env_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_env_293_);
lean_dec(v___x_292_);
v___x_294_ = lean_st_ref_get(v___y_288_);
v_mctx_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_mctx_295_);
lean_dec(v___x_294_);
v_lctx_296_ = lean_ctor_get(v___y_287_, 2);
v_options_297_ = lean_ctor_get(v___y_289_, 2);
lean_inc_ref(v_options_297_);
lean_inc_ref(v_lctx_296_);
v___x_298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_298_, 0, v_env_293_);
lean_ctor_set(v___x_298_, 1, v_mctx_295_);
lean_ctor_set(v___x_298_, 2, v_lctx_296_);
lean_ctor_set(v___x_298_, 3, v_options_297_);
v___x_299_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_msgData_286_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* v_msgData_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_ref_314_; lean_object* v___x_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_ref_314_ = lean_ctor_get(v___y_311_, 5);
v___x_315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msg_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_inc(v_ref_314_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_ref_314_);
lean_ctor_set(v___x_320_, 1, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 1);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2));
v___x_337_ = l_Lean_stringToMessageData(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* v_e_338_, lean_object* v_f_339_, lean_object* v_a_340_, lean_object* v_f_x27_341_, lean_object* v_hf_342_, uint8_t v_done_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; 
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc_ref(v_f_339_);
v___x_351_ = l_Lean_Meta_Sym_inferType___redArg(v_f_339_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
v___x_353_ = l_Lean_Meta_whnfD(v_a_352_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_353_);
if (lean_obj_tag(v_a_354_) == 7)
{
lean_object* v_binderName_355_; lean_object* v_body_356_; lean_object* v___x_357_; 
v_binderName_355_ = lean_ctor_get(v_a_354_, 0);
lean_inc(v_binderName_355_);
v_body_356_ = lean_ctor_get(v_a_354_, 2);
lean_inc_ref(v_body_356_);
lean_dec_ref(v_a_354_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc_ref(v_a_340_);
v___x_357_ = l_Lean_Meta_Sym_inferType___redArg(v_a_340_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc(v_a_358_);
v___x_359_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_358_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_359_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
v___x_361_ = l_Lean_Meta_Sym_inferType___redArg(v_e_338_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
v___x_363_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_362_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref(v___x_363_);
lean_inc_ref(v_a_340_);
lean_inc_ref(v_f_x27_341_);
v___x_365_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_x27_341_, v_a_340_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_382_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_382_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_370_ = 0;
lean_inc(v_a_358_);
v___x_371_ = l_Lean_mkLambda(v_binderName_355_, v___x_370_, v_a_358_, v_body_356_);
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v_a_364_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v_a_360_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_mkConst(v___x_372_, v___x_375_);
v___x_377_ = l_Lean_mkApp6(v___x_376_, v_a_358_, v___x_371_, v_f_339_, v_f_x27_341_, v_hf_342_, v_a_340_);
v___x_378_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_378_, 0, v_a_366_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*2, v_done_343_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_378_);
v___x_380_ = v___x_368_;
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
lean_dec(v_a_364_);
lean_dec(v_a_360_);
lean_dec(v_a_358_);
lean_dec_ref(v_body_356_);
lean_dec(v_binderName_355_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
v_a_383_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_365_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_365_);
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
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_a_360_);
lean_dec(v_a_358_);
lean_dec_ref(v_body_356_);
lean_dec(v_binderName_355_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
v_a_391_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_363_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_363_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_360_);
lean_dec(v_a_358_);
lean_dec_ref(v_body_356_);
lean_dec(v_binderName_355_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
v_a_399_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_361_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_361_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_a_358_);
lean_dec_ref(v_body_356_);
lean_dec(v_binderName_355_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
lean_dec_ref(v_e_338_);
v_a_407_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_359_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_359_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v_body_356_);
lean_dec(v_binderName_355_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
lean_dec_ref(v_e_338_);
v_a_415_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_357_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_357_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_a_354_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_e_338_);
v___x_423_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
v___x_424_ = l_Lean_indentExpr(v_f_339_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_425_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v___x_426_;
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
lean_dec_ref(v_e_338_);
v_a_427_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_353_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_353_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_hf_342_);
lean_dec_ref(v_f_x27_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_f_339_);
lean_dec_ref(v_e_338_);
v_a_435_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_351_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_351_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* v_e_443_, lean_object* v_f_444_, lean_object* v_a_445_, lean_object* v_f_x27_446_, lean_object* v_hf_447_, lean_object* v_done_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
uint8_t v_done_boxed_456_; lean_object* v_res_457_; 
v_done_boxed_456_ = lean_unbox(v_done_448_);
v_res_457_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_443_, v_f_444_, v_a_445_, v_f_x27_446_, v_hf_447_, v_done_boxed_456_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* v_e_458_, lean_object* v_f_459_, lean_object* v_a_460_, lean_object* v_f_x27_461_, lean_object* v_hf_462_, lean_object* v_x_463_, uint8_t v_done_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_458_, v_f_459_, v_a_460_, v_f_x27_461_, v_hf_462_, v_done_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* v_e_473_, lean_object* v_f_474_, lean_object* v_a_475_, lean_object* v_f_x27_476_, lean_object* v_hf_477_, lean_object* v_x_478_, lean_object* v_done_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
uint8_t v_done_boxed_487_; lean_object* v_res_488_; 
v_done_boxed_487_ = lean_unbox(v_done_479_);
v_res_488_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(v_e_473_, v_f_474_, v_a_475_, v_f_x27_476_, v_hf_477_, v_x_478_, v_done_boxed_487_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* v_00_u03b1_489_, lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_490_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* v_00_u03b1_499_, lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(v_00_u03b1_499_, v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_508_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_9068__overap_522_; lean_object* v___x_523_; 
v___x_521_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_9068__overap_522_ = lean_panic_fn(v___x_521_, v_msg_510_);
v___x_523_ = lean_apply_10(v___x_9068__overap_522_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, lean_box(0));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v_res_535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_540_ = lean_unsigned_to_nat(55u);
v___x_541_ = lean_unsigned_to_nat(119u);
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_544_ = l_mkPanicMessageWithDecl(v___x_543_, v___x_542_, v___x_541_, v___x_540_, v___x_539_);
return v___x_544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_546_ = lean_unsigned_to_nat(13u);
v___x_547_ = lean_unsigned_to_nat(128u);
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_550_ = l_mkPanicMessageWithDecl(v___x_549_, v___x_548_, v___x_547_, v___x_546_, v___x_545_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* v_simpFn_551_, lean_object* v_e_552_, lean_object* v_i_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_nat_dec_eq(v_i_553_, v___x_564_);
if (v___x_565_ == 0)
{
if (lean_obj_tag(v_e_552_) == 5)
{
lean_object* v_fn_566_; lean_object* v_arg_567_; lean_object* v___x_568_; lean_object* v_i_569_; lean_object* v___x_570_; 
v_fn_566_ = lean_ctor_get(v_e_552_, 0);
lean_inc_ref(v_fn_566_);
v_arg_567_ = lean_ctor_get(v_e_552_, 1);
lean_inc_ref(v_arg_567_);
v___x_568_ = lean_unsigned_to_nat(1u);
v_i_569_ = lean_nat_sub(v_i_553_, v___x_568_);
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
lean_inc(v_a_558_);
lean_inc_ref(v_a_557_);
lean_inc(v_a_556_);
lean_inc_ref(v_a_555_);
lean_inc(v_a_554_);
lean_inc_ref(v_fn_566_);
v___x_570_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_551_, v_fn_566_, v_i_569_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_i_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
lean_inc_ref(v_fn_566_);
v___x_572_ = l_Lean_Meta_Sym_inferType___redArg(v_fn_566_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
v___x_574_ = l_Lean_Meta_whnfD(v_a_573_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_614_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_614_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_614_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_614_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
if (lean_obj_tag(v_a_575_) == 7)
{
lean_object* v_binderType_579_; lean_object* v_body_580_; uint8_t v___x_598_; 
v_binderType_579_ = lean_ctor_get(v_a_575_, 1);
lean_inc_ref(v_binderType_579_);
v_body_580_ = lean_ctor_get(v_a_575_, 2);
lean_inc_ref(v_body_580_);
lean_dec_ref(v_a_575_);
v___x_598_ = l_Lean_Expr_hasLooseBVars(v_body_580_);
lean_dec_ref(v_body_580_);
if (v___x_598_ == 0)
{
lean_del_object(v___x_577_);
goto v___jp_581_;
}
else
{
if (v___x_565_ == 0)
{
lean_dec_ref(v_binderType_579_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
if (lean_obj_tag(v_a_571_) == 0)
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_e_552_);
lean_dec_ref(v_fn_566_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
v_isSharedCheck_608_ = !lean_is_exclusive(v_a_571_);
if (v_isSharedCheck_608_ == 0)
{
v___x_600_ = v_a_571_;
v_isShared_601_ = v_isSharedCheck_608_;
goto v_resetjp_599_;
}
else
{
lean_dec(v_a_571_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_608_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 0, 1);
v___x_603_ = v_reuseFailAlloc_607_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
lean_ctor_set_uint8(v___x_603_, 0, v___x_565_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_603_);
v___x_605_ = v___x_577_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_e_x27_609_; lean_object* v_proof_610_; lean_object* v___x_611_; 
lean_del_object(v___x_577_);
v_e_x27_609_ = lean_ctor_get(v_a_571_, 0);
lean_inc_ref(v_e_x27_609_);
v_proof_610_ = lean_ctor_get(v_a_571_, 1);
lean_inc_ref(v_proof_610_);
lean_dec_ref(v_a_571_);
v___x_611_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_552_, v_fn_566_, v_arg_567_, v_e_x27_609_, v_proof_610_, v___x_565_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_611_;
}
}
else
{
lean_del_object(v___x_577_);
goto v___jp_581_;
}
}
v___jp_581_:
{
lean_object* v___x_582_; 
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
v___x_582_ = l_Lean_Meta_isProp(v_binderType_579_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; uint8_t v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref(v___x_582_);
v___x_584_ = lean_unbox(v_a_583_);
lean_dec(v_a_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
lean_inc(v_a_558_);
lean_inc_ref(v_a_557_);
lean_inc_ref(v_arg_567_);
v___x_585_ = lean_sym_simp(v_arg_567_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref(v___x_585_);
v___x_587_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_552_, v_fn_566_, v_arg_567_, v_a_571_, v_a_586_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_587_;
}
else
{
lean_dec(v_a_571_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_fn_566_);
lean_dec_ref(v_e_552_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v___x_585_;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
v___x_588_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_588_, 0, v___x_565_);
v___x_589_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_552_, v_fn_566_, v_arg_567_, v_a_571_, v___x_588_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_589_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_571_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_fn_566_);
lean_dec_ref(v_e_552_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
v_a_590_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_582_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_582_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_577_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_e_552_);
lean_dec_ref(v_fn_566_);
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
v___x_613_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_612_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_613_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_a_571_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_fn_566_);
lean_dec_ref(v_e_552_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
v_a_615_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_574_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_574_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_571_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_fn_566_);
lean_dec_ref(v_e_552_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
v_a_623_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_572_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_572_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_e_552_);
lean_dec_ref(v_fn_566_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
return v___x_570_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v_e_552_);
lean_dec_ref(v_simpFn_551_);
v___x_631_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
v___x_632_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_631_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_632_;
}
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_apply_11(v_simpFn_551_, v_e_552_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, lean_box(0));
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* v_simpFn_634_, lean_object* v_e_635_, lean_object* v_i_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_634_, v_e_635_, v_i_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_i_636_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* v_e_648_, lean_object* v_numArgs_649_, lean_object* v_simpFn_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_650_, v_e_648_, v_numArgs_649_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* v_e_662_, lean_object* v_numArgs_663_, lean_object* v_simpFn_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_662_, v_numArgs_663_, v_simpFn_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_numArgs_663_);
return v_res_675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_678_ = lean_unsigned_to_nat(13u);
v___x_679_ = lean_unsigned_to_nat(165u);
v___x_680_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
v___x_681_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_682_ = l_mkPanicMessageWithDecl(v___x_681_, v___x_680_, v___x_679_, v___x_678_, v___x_677_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* v_simpFn_683_, lean_object* v_e_684_, lean_object* v_i_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v_i_685_, v___x_696_);
if (v___x_697_ == 0)
{
if (lean_obj_tag(v_e_684_) == 5)
{
lean_object* v_fn_698_; lean_object* v_arg_699_; lean_object* v___x_700_; lean_object* v_i_701_; lean_object* v___x_702_; 
v_fn_698_ = lean_ctor_get(v_e_684_, 0);
lean_inc_ref(v_fn_698_);
v_arg_699_ = lean_ctor_get(v_e_684_, 1);
lean_inc_ref(v_arg_699_);
v___x_700_ = lean_unsigned_to_nat(1u);
v_i_701_ = lean_nat_sub(v_i_685_, v___x_700_);
lean_inc(v_a_694_);
lean_inc_ref(v_a_693_);
lean_inc(v_a_692_);
lean_inc_ref(v_a_691_);
lean_inc(v_a_690_);
lean_inc_ref(v_a_689_);
lean_inc_ref(v_fn_698_);
v___x_702_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_683_, v_fn_698_, v_i_701_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_i_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
if (lean_obj_tag(v_a_703_) == 0)
{
lean_dec_ref(v_a_703_);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_e_684_);
lean_dec_ref(v_fn_698_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
return v___x_702_;
}
else
{
lean_object* v_e_x27_704_; lean_object* v_proof_705_; uint8_t v_done_706_; lean_object* v___x_707_; 
lean_dec_ref(v___x_702_);
v_e_x27_704_ = lean_ctor_get(v_a_703_, 0);
lean_inc_ref(v_e_x27_704_);
v_proof_705_ = lean_ctor_get(v_a_703_, 1);
lean_inc_ref(v_proof_705_);
v_done_706_ = lean_ctor_get_uint8(v_a_703_, sizeof(void*)*2);
lean_dec_ref(v_a_703_);
v___x_707_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_684_, v_fn_698_, v_arg_699_, v_e_x27_704_, v_proof_705_, v_done_706_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
return v___x_707_;
}
}
else
{
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_fn_698_);
lean_dec_ref(v_e_684_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
return v___x_702_;
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec_ref(v_e_684_);
lean_dec_ref(v_simpFn_683_);
v___x_708_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
v___x_709_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_708_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
return v___x_709_;
}
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_apply_11(v_simpFn_683_, v_e_684_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, lean_box(0));
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* v_simpFn_711_, lean_object* v_e_712_, lean_object* v_i_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_711_, v_e_712_, v_i_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_i_713_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* v_e_725_, lean_object* v_numArgs_726_, lean_object* v_simpFn_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_727_, v_e_725_, v_numArgs_726_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* v_e_739_, lean_object* v_numArgs_740_, lean_object* v_simpFn_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_739_, v_numArgs_740_, v_simpFn_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_numArgs_740_);
return v_res_752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(lean_object* v_type_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = l_Lean_Expr_isForall(v_type_756_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_inc(v_a_761_);
lean_inc_ref(v_a_760_);
lean_inc(v_a_759_);
lean_inc_ref(v_a_758_);
v___x_764_ = l_Lean_Meta_whnfD(v_type_756_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; uint8_t v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
v___x_766_ = l_Lean_Expr_isForall(v_a_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1);
v___x_768_ = l_Lean_MessageData_ofExpr(v_a_765_);
v___x_769_ = l_Lean_indentD(v___x_768_);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_770_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v___x_780_; 
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
v___x_780_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_765_, v_a_757_);
return v___x_780_;
}
}
else
{
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v___x_764_;
}
}
else
{
lean_object* v___x_781_; 
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v_type_756_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___boxed(lean_object* v_type_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_type_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_type_790_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_807_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_toApplicative_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_886_; 
v___x_821_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_822_ = l_ReaderT_instMonad___redArg(v___x_821_);
v_toApplicative_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_822_, 1);
lean_dec(v_unused_887_);
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_886_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_toApplicative_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_886_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_toFunctor_827_; lean_object* v_toSeq_828_; lean_object* v_toSeqLeft_829_; lean_object* v_toSeqRight_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_884_; 
v_toFunctor_827_ = lean_ctor_get(v_toApplicative_823_, 0);
v_toSeq_828_ = lean_ctor_get(v_toApplicative_823_, 2);
v_toSeqLeft_829_ = lean_ctor_get(v_toApplicative_823_, 3);
v_toSeqRight_830_ = lean_ctor_get(v_toApplicative_823_, 4);
v_isSharedCheck_884_ = !lean_is_exclusive(v_toApplicative_823_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_toApplicative_823_, 1);
lean_dec(v_unused_885_);
v___x_832_ = v_toApplicative_823_;
v_isShared_833_ = v_isSharedCheck_884_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_toSeqRight_830_);
lean_inc(v_toSeqLeft_829_);
lean_inc(v_toSeq_828_);
lean_inc(v_toFunctor_827_);
lean_dec(v_toApplicative_823_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_884_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___x_843_; 
v___f_834_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1));
v___f_835_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_827_);
v___f_836_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_836_, 0, v_toFunctor_827_);
v___f_837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_837_, 0, v_toFunctor_827_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___f_836_);
lean_ctor_set(v___x_838_, 1, v___f_837_);
v___f_839_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_839_, 0, v_toSeqRight_830_);
v___f_840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_840_, 0, v_toSeqLeft_829_);
v___f_841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_841_, 0, v_toSeq_828_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 4, v___f_839_);
lean_ctor_set(v___x_832_, 3, v___f_840_);
lean_ctor_set(v___x_832_, 2, v___f_841_);
lean_ctor_set(v___x_832_, 1, v___f_834_);
lean_ctor_set(v___x_832_, 0, v___x_838_);
v___x_843_ = v___x_832_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___f_834_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v___f_841_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v___f_840_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v___f_839_);
v___x_843_ = v_reuseFailAlloc_883_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___f_835_);
lean_ctor_set(v___x_825_, 0, v___x_843_);
v___x_845_ = v___x_825_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___f_835_);
v___x_845_ = v_reuseFailAlloc_882_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v_toApplicative_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_880_; 
v___x_846_ = l_ReaderT_instMonad___redArg(v___x_845_);
v_toApplicative_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v___x_846_, 1);
lean_dec(v_unused_881_);
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_880_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_toApplicative_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_880_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_toFunctor_851_; lean_object* v_toSeq_852_; lean_object* v_toSeqLeft_853_; lean_object* v_toSeqRight_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_878_; 
v_toFunctor_851_ = lean_ctor_get(v_toApplicative_847_, 0);
v_toSeq_852_ = lean_ctor_get(v_toApplicative_847_, 2);
v_toSeqLeft_853_ = lean_ctor_get(v_toApplicative_847_, 3);
v_toSeqRight_854_ = lean_ctor_get(v_toApplicative_847_, 4);
v_isSharedCheck_878_ = !lean_is_exclusive(v_toApplicative_847_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_toApplicative_847_, 1);
lean_dec(v_unused_879_);
v___x_856_ = v_toApplicative_847_;
v_isShared_857_ = v_isSharedCheck_878_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_toSeqRight_854_);
lean_inc(v_toSeqLeft_853_);
lean_inc(v_toSeq_852_);
lean_inc(v_toFunctor_851_);
lean_dec(v_toApplicative_847_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_878_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___x_867_; 
v___f_858_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3));
v___f_859_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_851_);
v___f_860_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_860_, 0, v_toFunctor_851_);
v___f_861_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_861_, 0, v_toFunctor_851_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___f_860_);
lean_ctor_set(v___x_862_, 1, v___f_861_);
v___f_863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_863_, 0, v_toSeqRight_854_);
v___f_864_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_864_, 0, v_toSeqLeft_853_);
v___f_865_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_865_, 0, v_toSeq_852_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 4, v___f_863_);
lean_ctor_set(v___x_856_, 3, v___f_864_);
lean_ctor_set(v___x_856_, 2, v___f_865_);
lean_ctor_set(v___x_856_, 1, v___f_858_);
lean_ctor_set(v___x_856_, 0, v___x_862_);
v___x_867_ = v___x_856_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___f_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v___f_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v___f_864_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v___f_863_);
v___x_867_ = v_reuseFailAlloc_877_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___f_859_);
lean_ctor_set(v___x_849_, 0, v___x_867_);
v___x_869_ = v___x_849_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___f_859_);
v___x_869_ = v_reuseFailAlloc_876_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_1009__overap_874_; lean_object* v___x_875_; 
v___x_870_ = l_ReaderT_instMonad___redArg(v___x_869_);
v___x_871_ = l_Lean_instInhabitedExpr;
v___x_872_ = l_instInhabitedOfMonad___redArg(v___x_870_, v___x_871_);
v___f_873_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_873_, 0, v___x_872_);
v___x_1009__overap_874_ = lean_panic_fn(v___f_873_, v_msg_813_);
v___x_875_ = lean_apply_7(v___x_1009__overap_874_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, lean_box(0));
return v___x_875_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v_res_896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_899_ = lean_unsigned_to_nat(47u);
v___x_900_ = lean_unsigned_to_nat(196u);
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_903_ = l_mkPanicMessageWithDecl(v___x_902_, v___x_901_, v___x_900_, v___x_899_, v___x_898_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_904_, lean_object* v_n_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_zero_913_; uint8_t v_isZero_914_; 
v_zero_913_ = lean_unsigned_to_nat(0u);
v_isZero_914_ = lean_nat_dec_eq(v_n_905_, v_zero_913_);
if (v_isZero_914_ == 1)
{
lean_object* v___x_915_; 
lean_dec_ref(v_a_906_);
v___x_915_ = l_Lean_Meta_Sym_inferType___redArg(v_e_904_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_907_);
return v___x_915_;
}
else
{
lean_object* v_one_916_; lean_object* v_n_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_one_916_ = lean_unsigned_to_nat(1u);
v_n_917_ = lean_nat_sub(v_n_905_, v_one_916_);
v___x_918_ = l_Lean_Expr_appFn_x21(v_e_904_);
lean_dec_ref(v_e_904_);
lean_inc(v_a_911_);
lean_inc_ref(v_a_910_);
lean_inc(v_a_909_);
lean_inc_ref(v_a_908_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
v___x_919_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_918_, v_n_917_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_n_917_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
lean_inc(v_a_911_);
lean_inc_ref(v_a_910_);
lean_inc(v_a_909_);
lean_inc_ref(v_a_908_);
v___x_921_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_a_920_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_932_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_932_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
if (lean_obj_tag(v_a_922_) == 7)
{
lean_object* v_body_926_; lean_object* v___x_928_; 
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
v_body_926_ = lean_ctor_get(v_a_922_, 2);
lean_inc_ref(v_body_926_);
lean_dec_ref(v_a_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_body_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_body_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_del_object(v___x_924_);
lean_dec(v_a_922_);
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_931_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_930_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
return v___x_931_;
}
}
}
else
{
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v___x_921_;
}
}
else
{
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_933_, lean_object* v_n_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_933_, v_n_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_n_934_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_943_, lean_object* v_a_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___y_953_; lean_object* v___x_956_; uint8_t v_debug_957_; 
v___x_956_ = lean_st_ref_get(v___y_946_);
v_debug_957_ = lean_ctor_get_uint8(v___x_956_, sizeof(void*)*7);
lean_dec(v___x_956_);
if (v_debug_957_ == 0)
{
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v___y_945_);
v___y_953_ = v___y_946_;
goto v___jp_952_;
}
else
{
lean_object* v___x_958_; 
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc_ref(v_f_943_);
v___x_958_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_943_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v___x_958_);
lean_inc(v___y_946_);
lean_inc_ref(v_a_944_);
v___x_959_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_dec_ref(v___x_959_);
v___y_953_ = v___y_946_;
goto v___jp_952_;
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v___y_946_);
lean_dec_ref(v_a_944_);
lean_dec_ref(v_f_943_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_a_944_);
lean_dec_ref(v_f_943_);
v_a_968_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_958_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_958_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
v___jp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Lean_Expr_app___override(v_f_943_, v_a_944_);
v___x_955_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_954_, v___y_953_);
lean_dec(v___y_953_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_976_, lean_object* v_a_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_976_, v_a_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_986_, lean_object* v_a_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_986_, v_a_987_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_999_, lean_object* v_a_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_999_, v_a_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
return v_res_1011_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_30334__overap_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
v___x_30334__overap_1025_ = lean_panic_fn(v___x_1024_, v_msg_1013_);
v___x_1026_ = lean_apply_10(v___x_30334__overap_1025_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v_res_1038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_1044_ = l_Lean_Expr_const___override(v___x_1043_, v___x_1042_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1047_ = lean_unsigned_to_nat(52u);
v___x_1048_ = lean_unsigned_to_nat(256u);
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1051_ = l_mkPanicMessageWithDecl(v___x_1050_, v___x_1049_, v___x_1048_, v___x_1047_, v___x_1046_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1053_ = lean_unsigned_to_nat(52u);
v___x_1054_ = lean_unsigned_to_nat(248u);
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1056_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1057_ = l_mkPanicMessageWithDecl(v___x_1056_, v___x_1055_, v___x_1054_, v___x_1053_, v___x_1052_);
return v___x_1057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1059_ = lean_unsigned_to_nat(52u);
v___x_1060_ = lean_unsigned_to_nat(263u);
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1062_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1063_ = l_mkPanicMessageWithDecl(v___x_1062_, v___x_1061_, v___x_1060_, v___x_1059_, v___x_1058_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1065_ = lean_unsigned_to_nat(26u);
v___x_1066_ = lean_unsigned_to_nat(243u);
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1069_ = l_mkPanicMessageWithDecl(v___x_1068_, v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1071_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1073_, lean_object* v_e_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_nat_dec_eq(v_i_1073_, v___x_1085_);
if (v___x_1086_ == 0)
{
if (lean_obj_tag(v_e_1074_) == 5)
{
lean_object* v_fn_1087_; lean_object* v_arg_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_fn_1087_ = lean_ctor_get(v_e_1074_, 0);
lean_inc_ref(v_fn_1087_);
v_arg_1088_ = lean_ctor_get(v_e_1074_, 1);
lean_inc_ref(v_arg_1088_);
lean_dec_ref(v_e_1074_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_sub(v_i_1073_, v___x_1089_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc_ref(v_a_1078_);
lean_inc(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc_ref(v_fn_1087_);
v___x_1091_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1090_, v_fn_1087_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1346_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v_fst_1093_ = lean_ctor_get(v_a_1092_, 0);
v_snd_1094_ = lean_ctor_get(v_a_1092_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1096_ = v_a_1092_;
v_isShared_1097_ = v_isSharedCheck_1346_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v_a_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1346_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; 
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc_ref(v_a_1078_);
lean_inc(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc_ref(v_arg_1088_);
v___x_1098_ = lean_sym_simp(v_arg_1088_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1098_) == 0)
{
if (lean_obj_tag(v_fst_1093_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_fst_1093_);
lean_dec(v_snd_1094_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1196_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1196_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
if (lean_obj_tag(v_a_1099_) == 0)
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v___x_1090_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_a_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1104_ = v_a_1099_;
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_a_1099_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 0, 1);
v___x_1107_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_ctor_set_uint8(v___x_1107_, 0, v___x_1086_);
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1108_);
lean_ctor_set(v___x_1096_, 0, v___x_1107_);
v___x_1110_ = v___x_1096_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1110_);
v___x_1112_ = v___x_1101_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1117_; lean_object* v_proof_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1195_; 
lean_del_object(v___x_1101_);
v_e_x27_1117_ = lean_ctor_get(v_a_1099_, 0);
v_proof_1118_ = lean_ctor_get(v_a_1099_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1099_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1120_ = v_a_1099_;
v_isShared_1121_ = v_isSharedCheck_1195_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_proof_1118_);
lean_inc(v_e_x27_1117_);
lean_dec(v_a_1099_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1195_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; 
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc_ref(v_a_1078_);
lean_inc_ref(v_fn_1087_);
v___x_1122_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1087_, v___x_1090_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v___x_1090_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1122_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
v___x_1124_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_a_1123_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref(v___x_1124_);
if (lean_obj_tag(v_a_1125_) == 7)
{
lean_object* v_binderType_1126_; lean_object* v_body_1127_; lean_object* v___x_1128_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_binderType_1126_ = lean_ctor_get(v_a_1125_, 1);
lean_inc_ref(v_binderType_1126_);
v_body_1127_ = lean_ctor_get(v_a_1125_, 2);
lean_inc_ref(v_body_1127_);
lean_dec_ref(v_a_1125_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc_ref(v_e_x27_1117_);
lean_inc_ref(v_fn_1087_);
v___x_1128_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1087_, v_e_x27_1117_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc_ref(v_binderType_1126_);
v___x_1130_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1126_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
lean_inc_ref(v_body_1127_);
v___x_1132_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1127_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1152_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1152_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1152_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1133_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_a_1131_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_mkConst(v___x_1137_, v___x_1140_);
lean_inc_ref(v_body_1127_);
v___x_1142_ = l_Lean_mkApp6(v___x_1141_, v_binderType_1126_, v_body_1127_, v_arg_1088_, v_e_x27_1117_, v_fn_1087_, v_proof_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1142_);
lean_ctor_set(v___x_1120_, 0, v_a_1129_);
v___x_1144_ = v___x_1120_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1129_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2, v___x_1086_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_body_1127_);
lean_ctor_set(v___x_1096_, 0, v___x_1144_);
v___x_1146_ = v___x_1096_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_body_1127_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1146_);
v___x_1148_ = v___x_1135_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_a_1131_);
lean_dec(v_a_1129_);
lean_dec_ref(v_body_1127_);
lean_dec_ref(v_binderType_1126_);
lean_del_object(v___x_1120_);
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
v_a_1153_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1132_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1132_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v_a_1129_);
lean_dec_ref(v_body_1127_);
lean_dec_ref(v_binderType_1126_);
lean_del_object(v___x_1120_);
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
v_a_1161_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1130_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1130_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_body_1127_);
lean_dec_ref(v_binderType_1126_);
lean_del_object(v___x_1120_);
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
v_a_1169_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1128_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1128_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_a_1125_);
lean_del_object(v___x_1120_);
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
v___x_1177_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1178_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1177_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1178_;
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_del_object(v___x_1120_);
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_a_1179_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1124_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1124_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_del_object(v___x_1120_);
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_a_1187_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1122_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1122_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1197_; 
lean_dec(v___x_1090_);
v_a_1197_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1098_);
if (lean_obj_tag(v_a_1197_) == 0)
{
lean_object* v_e_x27_1198_; lean_object* v_proof_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_a_1197_);
v_e_x27_1198_ = lean_ctor_get(v_fst_1093_, 0);
v_proof_1199_ = lean_ctor_get(v_fst_1093_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_fst_1093_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1201_ = v_fst_1093_;
v_isShared_1202_ = v_isSharedCheck_1266_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_proof_1199_);
lean_inc(v_e_x27_1198_);
lean_dec(v_fst_1093_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1266_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; 
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
v___x_1203_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_snd_1094_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
if (lean_obj_tag(v_a_1204_) == 7)
{
lean_object* v_binderType_1205_; lean_object* v_body_1206_; lean_object* v___x_1207_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_binderType_1205_ = lean_ctor_get(v_a_1204_, 1);
lean_inc_ref(v_binderType_1205_);
v_body_1206_ = lean_ctor_get(v_a_1204_, 2);
lean_inc_ref(v_body_1206_);
lean_dec_ref(v_a_1204_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc_ref(v_arg_1088_);
lean_inc_ref(v_e_x27_1198_);
v___x_1207_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1198_, v_arg_1088_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc_ref(v_binderType_1205_);
v___x_1209_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1205_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
lean_inc_ref(v_body_1206_);
v___x_1211_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1206_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1231_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1231_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1231_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1216_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1212_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_a_1210_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_mkConst(v___x_1216_, v___x_1219_);
lean_inc_ref(v_body_1206_);
v___x_1221_ = l_Lean_mkApp6(v___x_1220_, v_binderType_1205_, v_body_1206_, v_fn_1087_, v_e_x27_1198_, v_proof_1199_, v_arg_1088_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1221_);
lean_ctor_set(v___x_1201_, 0, v_a_1208_);
v___x_1223_ = v___x_1201_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1208_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*2, v___x_1086_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_body_1206_);
lean_ctor_set(v___x_1096_, 0, v___x_1223_);
v___x_1225_ = v___x_1096_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_body_1206_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1225_);
v___x_1227_ = v___x_1214_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1210_);
lean_dec(v_a_1208_);
lean_dec_ref(v_body_1206_);
lean_dec_ref(v_binderType_1205_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_proof_1199_);
lean_dec_ref(v_e_x27_1198_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
v_a_1232_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1211_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1211_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1208_);
lean_dec_ref(v_body_1206_);
lean_dec_ref(v_binderType_1205_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_proof_1199_);
lean_dec_ref(v_e_x27_1198_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
v_a_1240_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1209_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1209_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_body_1206_);
lean_dec_ref(v_binderType_1205_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_proof_1199_);
lean_dec_ref(v_e_x27_1198_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
v_a_1248_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1207_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1207_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec(v_a_1204_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_proof_1199_);
lean_dec_ref(v_e_x27_1198_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1257_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1256_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1257_;
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1201_);
lean_dec_ref(v_proof_1199_);
lean_dec_ref(v_e_x27_1198_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_a_1258_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1203_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1203_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1267_; lean_object* v_proof_1268_; lean_object* v_e_x27_1269_; lean_object* v_proof_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1337_; 
v_e_x27_1267_ = lean_ctor_get(v_fst_1093_, 0);
lean_inc_ref(v_e_x27_1267_);
v_proof_1268_ = lean_ctor_get(v_fst_1093_, 1);
lean_inc_ref(v_proof_1268_);
lean_dec_ref(v_fst_1093_);
v_e_x27_1269_ = lean_ctor_get(v_a_1197_, 0);
v_proof_1270_ = lean_ctor_get(v_a_1197_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1272_ = v_a_1197_;
v_isShared_1273_ = v_isSharedCheck_1337_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_proof_1270_);
lean_inc(v_e_x27_1269_);
lean_dec(v_a_1197_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1337_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; 
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
v___x_1274_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_snd_1094_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
if (lean_obj_tag(v_a_1275_) == 7)
{
lean_object* v_binderType_1276_; lean_object* v_body_1277_; lean_object* v___x_1278_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_binderType_1276_ = lean_ctor_get(v_a_1275_, 1);
lean_inc_ref(v_binderType_1276_);
v_body_1277_ = lean_ctor_get(v_a_1275_, 2);
lean_inc_ref(v_body_1277_);
lean_dec_ref(v_a_1275_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc_ref(v_e_x27_1269_);
lean_inc_ref(v_e_x27_1267_);
v___x_1278_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1267_, v_e_x27_1269_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc_ref(v_binderType_1276_);
v___x_1280_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1276_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
lean_inc_ref(v_body_1277_);
v___x_1282_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1277_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1302_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1302_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1302_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1287_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_a_1283_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_a_1281_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_mkConst(v___x_1287_, v___x_1290_);
lean_inc_ref(v_body_1277_);
v___x_1292_ = l_Lean_mkApp8(v___x_1291_, v_binderType_1276_, v_body_1277_, v_fn_1087_, v_e_x27_1267_, v_arg_1088_, v_e_x27_1269_, v_proof_1268_, v_proof_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1292_);
lean_ctor_set(v___x_1272_, 0, v_a_1279_);
v___x_1294_ = v___x_1272_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*2, v___x_1086_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_body_1277_);
lean_ctor_set(v___x_1096_, 0, v___x_1294_);
v___x_1296_ = v___x_1096_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_body_1277_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1296_);
v___x_1298_ = v___x_1285_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_a_1281_);
lean_dec(v_a_1279_);
lean_dec_ref(v_body_1277_);
lean_dec_ref(v_binderType_1276_);
lean_del_object(v___x_1272_);
lean_dec_ref(v_proof_1270_);
lean_dec_ref(v_e_x27_1269_);
lean_dec_ref(v_proof_1268_);
lean_dec_ref(v_e_x27_1267_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
v_a_1303_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1282_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1282_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1279_);
lean_dec_ref(v_body_1277_);
lean_dec_ref(v_binderType_1276_);
lean_del_object(v___x_1272_);
lean_dec_ref(v_proof_1270_);
lean_dec_ref(v_e_x27_1269_);
lean_dec_ref(v_proof_1268_);
lean_dec_ref(v_e_x27_1267_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
v_a_1311_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1280_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1280_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_body_1277_);
lean_dec_ref(v_binderType_1276_);
lean_del_object(v___x_1272_);
lean_dec_ref(v_proof_1270_);
lean_dec_ref(v_e_x27_1269_);
lean_dec_ref(v_proof_1268_);
lean_dec_ref(v_e_x27_1267_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
v_a_1319_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1278_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1278_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v_a_1275_);
lean_del_object(v___x_1272_);
lean_dec_ref(v_proof_1270_);
lean_dec_ref(v_e_x27_1269_);
lean_dec_ref(v_proof_1268_);
lean_dec_ref(v_e_x27_1267_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
v___x_1327_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1328_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1327_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1328_;
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_del_object(v___x_1272_);
lean_dec_ref(v_proof_1270_);
lean_dec_ref(v_e_x27_1269_);
lean_dec_ref(v_proof_1268_);
lean_dec_ref(v_e_x27_1267_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_a_1329_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1274_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1274_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_del_object(v___x_1096_);
lean_dec(v_snd_1094_);
lean_dec(v_fst_1093_);
lean_dec(v___x_1090_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
v_a_1338_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1098_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1098_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_dec(v___x_1090_);
lean_dec_ref(v_arg_1088_);
lean_dec_ref(v_fn_1087_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
return v___x_1091_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v_e_1074_);
v___x_1347_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1348_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1347_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_e_1074_);
v___x_1349_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1351_, lean_object* v_e_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1351_, v_e_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_i_1351_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1364_, lean_object* v_e_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1364_, v_e_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1385_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_fst_1381_; lean_object* v___x_1383_; 
v_fst_1381_ = lean_ctor_get(v_a_1377_, 0);
lean_inc(v_fst_1381_);
lean_dec(v_a_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_fst_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_fst_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1376_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1376_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1394_, lean_object* v_e_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1394_, v_e_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_n_1394_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1407_, lean_object* v_prefixSize_1408_, lean_object* v_suffixSize_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_numArgs_1420_; uint8_t v___x_1421_; 
v_numArgs_1420_ = l_Lean_Expr_getAppNumArgs(v_e_1407_);
v___x_1421_ = lean_nat_dec_le(v_numArgs_1420_, v_prefixSize_1408_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = lean_nat_add(v_prefixSize_1408_, v_suffixSize_1409_);
v___x_1423_ = lean_nat_dec_lt(v___x_1422_, v_numArgs_1420_);
lean_dec(v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_suffixSize_1409_);
v___x_1424_ = lean_nat_sub(v_numArgs_1420_, v_prefixSize_1408_);
lean_dec(v_numArgs_1420_);
v___x_1425_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1424_, v_e_1407_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
lean_dec(v___x_1424_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = lean_nat_sub(v_numArgs_1420_, v_prefixSize_1408_);
lean_dec(v_numArgs_1420_);
v___x_1427_ = lean_nat_sub(v___x_1426_, v_suffixSize_1409_);
lean_dec(v___x_1426_);
v___x_1428_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1428_, 0, v_suffixSize_1409_);
v___x_1429_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1428_, v_e_1407_, v___x_1427_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
lean_dec(v___x_1427_);
return v___x_1429_;
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_numArgs_1420_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec(v_suffixSize_1409_);
lean_dec_ref(v_e_1407_);
v___x_1430_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1432_, lean_object* v_prefixSize_1433_, lean_object* v_suffixSize_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1432_, v_prefixSize_1433_, v_suffixSize_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_prefixSize_1433_);
return v_res_1445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1448_ = lean_unsigned_to_nat(13u);
v___x_1449_ = lean_unsigned_to_nat(298u);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1452_ = l_mkPanicMessageWithDecl(v___x_1451_, v___x_1450_, v___x_1449_, v___x_1448_, v___x_1447_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1453_, lean_object* v_i_1454_, lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_nat_dec_eq(v_i_1454_, v___x_1466_);
if (v___x_1467_ == 0)
{
if (lean_obj_tag(v_e_1455_) == 5)
{
lean_object* v_fn_1468_; lean_object* v_arg_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_fn_1468_ = lean_ctor_get(v_e_1455_, 0);
lean_inc_ref(v_fn_1468_);
v_arg_1469_ = lean_ctor_get(v_e_1455_, 1);
lean_inc_ref(v_arg_1469_);
v___x_1470_ = lean_unsigned_to_nat(1u);
v___x_1471_ = lean_nat_sub(v_i_1454_, v___x_1470_);
lean_inc(v_a_1464_);
lean_inc_ref(v_a_1463_);
lean_inc(v_a_1462_);
lean_inc_ref(v_a_1461_);
lean_inc(v_a_1460_);
lean_inc_ref(v_a_1459_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_fn_1468_);
v___x_1472_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1453_, v___x_1471_, v_fn_1468_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1497_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_array_fget_borrowed(v_rewritable_1453_, v___x_1471_);
lean_dec(v___x_1471_);
v___x_1478_ = lean_unbox(v___x_1477_);
if (v___x_1478_ == 0)
{
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
if (lean_obj_tag(v_a_1473_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_e_1455_);
lean_dec_ref(v_fn_1468_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_a_1473_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1480_ = v_a_1473_;
v_isShared_1481_ = v_isSharedCheck_1489_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_a_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1489_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 0, 1);
v___x_1483_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
uint8_t v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_unbox(v___x_1477_);
lean_ctor_set_uint8(v___x_1483_, 0, v___x_1484_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1483_);
v___x_1486_ = v___x_1475_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1483_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_e_x27_1490_; lean_object* v_proof_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; 
lean_del_object(v___x_1475_);
v_e_x27_1490_ = lean_ctor_get(v_a_1473_, 0);
lean_inc_ref(v_e_x27_1490_);
v_proof_1491_ = lean_ctor_get(v_a_1473_, 1);
lean_inc_ref(v_proof_1491_);
lean_dec_ref(v_a_1473_);
v___x_1492_ = lean_unbox(v___x_1477_);
v___x_1493_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1455_, v_fn_1468_, v_arg_1469_, v_e_x27_1490_, v_proof_1491_, v___x_1492_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1493_;
}
}
else
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1475_);
lean_inc(v_a_1464_);
lean_inc_ref(v_a_1463_);
lean_inc(v_a_1462_);
lean_inc_ref(v_a_1461_);
lean_inc(v_a_1460_);
lean_inc_ref(v_a_1459_);
lean_inc_ref(v_arg_1469_);
v___x_1494_ = lean_sym_simp(v_arg_1469_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1455_, v_fn_1468_, v_arg_1469_, v_a_1473_, v_a_1495_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1496_;
}
else
{
lean_dec(v_a_1473_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_fn_1468_);
lean_dec_ref(v_e_1455_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
return v___x_1494_;
}
}
}
}
else
{
lean_dec(v___x_1471_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_fn_1468_);
lean_dec_ref(v_e_1455_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
return v___x_1472_;
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v_e_1455_);
v___x_1498_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1499_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1498_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1499_;
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_e_1455_);
v___x_1500_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1502_, lean_object* v_i_1503_, lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1502_, v_i_1503_, v_e_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_i_1503_);
lean_dec_ref(v_rewritable_1502_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1516_, lean_object* v_i_1517_, lean_object* v_e_1518_, lean_object* v_h_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1516_, v_i_1517_, v_e_1518_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1531_, lean_object* v_i_1532_, lean_object* v_e_1533_, lean_object* v_h_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1531_, v_i_1532_, v_e_1533_, v_h_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_i_1532_);
lean_dec_ref(v_rewritable_1531_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1546_, lean_object* v___x_1547_, lean_object* v_x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1546_, v___x_1547_, v_x_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1560_, lean_object* v___x_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1560_, v___x_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___x_1561_);
lean_dec_ref(v_rewritable_1560_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1574_, lean_object* v_rewritable_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_numArgs_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_numArgs_1586_ = l_Lean_Expr_getAppNumArgs(v_e_1574_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_nat_dec_eq(v_numArgs_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_array_get_size(v_rewritable_1575_);
v___x_1590_ = lean_nat_dec_lt(v___x_1589_, v_numArgs_1586_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1575_, v_numArgs_1586_, v_e_1574_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_numArgs_1586_);
lean_dec_ref(v_rewritable_1575_);
return v___x_1591_;
}
else
{
lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___f_1592_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1592_, 0, v_rewritable_1575_);
lean_closure_set(v___f_1592_, 1, v___x_1589_);
v___x_1593_ = lean_nat_sub(v_numArgs_1586_, v___x_1589_);
lean_dec(v_numArgs_1586_);
v___x_1594_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1592_, v_e_1574_, v___x_1593_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v___x_1593_);
return v___x_1594_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_numArgs_1586_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_rewritable_1575_);
lean_dec_ref(v_e_1574_);
v___x_1595_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1597_, lean_object* v_rewritable_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1597_, v_rewritable_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1610_, lean_object* v_numEqs_1611_, lean_object* v_result_1612_){
_start:
{
if (lean_obj_tag(v_result_1612_) == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
lean_dec(v_numEqs_1611_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_array_get_size(v_argResults_1610_);
v___x_1615_ = lean_nat_dec_lt(v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_dec_ref(v_result_1612_);
return v_argResults_1610_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_array_push(v_argResults_1610_, v_result_1612_);
return v___x_1616_;
}
}
else
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = lean_array_get_size(v_argResults_1610_);
v___x_1618_ = lean_nat_dec_lt(v___x_1617_, v_numEqs_1611_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec(v_numEqs_1611_);
v___x_1619_ = lean_array_push(v_argResults_1610_, v_result_1612_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_argResults_1610_);
v___x_1620_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_1621_ = lean_mk_array(v_numEqs_1611_, v___x_1620_);
v___x_1622_ = lean_array_push(v___x_1621_, v_result_1612_);
return v___x_1622_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1625_ = lean_unsigned_to_nat(13u);
v___x_1626_ = lean_unsigned_to_nat(411u);
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1629_ = l_mkPanicMessageWithDecl(v___x_1628_, v___x_1627_, v___x_1626_, v___x_1625_, v___x_1624_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1630_, lean_object* v_mkNonRflResult_1631_, lean_object* v_e_1632_, lean_object* v_i_1633_, lean_object* v_numEqs_1634_, lean_object* v_argResults_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
if (lean_obj_tag(v_e_1632_) == 5)
{
lean_object* v_fn_1646_; lean_object* v_arg_1647_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_fn_1646_ = lean_ctor_get(v_e_1632_, 0);
lean_inc_ref(v_fn_1646_);
v_arg_1647_ = lean_ctor_get(v_e_1632_, 1);
lean_inc_ref(v_arg_1647_);
lean_dec_ref(v_e_1632_);
v___x_1661_ = 0;
v___x_1662_ = lean_box(v___x_1661_);
v___x_1663_ = lean_array_get_borrowed(v___x_1662_, v_argKinds_1630_, v_i_1633_);
v___x_1664_ = lean_unbox(v___x_1663_);
switch(v___x_1664_)
{
case 5:
{
lean_dec_ref(v_arg_1647_);
v___y_1649_ = v_a_1636_;
v___y_1650_ = v_a_1637_;
v___y_1651_ = v_a_1638_;
v___y_1652_ = v_a_1639_;
v___y_1653_ = v_a_1640_;
v___y_1654_ = v_a_1641_;
v___y_1655_ = v_a_1642_;
v___y_1656_ = v_a_1643_;
v___y_1657_ = v_a_1644_;
goto v___jp_1648_;
}
case 0:
{
lean_dec_ref(v_arg_1647_);
v___y_1649_ = v_a_1636_;
v___y_1650_ = v_a_1637_;
v___y_1651_ = v_a_1638_;
v___y_1652_ = v_a_1639_;
v___y_1653_ = v_a_1640_;
v___y_1654_ = v_a_1641_;
v___y_1655_ = v_a_1642_;
v___y_1656_ = v_a_1643_;
v___y_1657_ = v_a_1644_;
goto v___jp_1648_;
}
case 3:
{
lean_dec_ref(v_arg_1647_);
v___y_1649_ = v_a_1636_;
v___y_1650_ = v_a_1637_;
v___y_1651_ = v_a_1638_;
v___y_1652_ = v_a_1639_;
v___y_1653_ = v_a_1640_;
v___y_1654_ = v_a_1641_;
v___y_1655_ = v_a_1642_;
v___y_1656_ = v_a_1643_;
v___y_1657_ = v_a_1644_;
goto v___jp_1648_;
}
case 2:
{
lean_object* v___x_1665_; 
lean_inc(v_a_1644_);
lean_inc_ref(v_a_1643_);
lean_inc(v_a_1642_);
lean_inc_ref(v_a_1641_);
lean_inc(v_a_1640_);
lean_inc_ref(v_a_1639_);
lean_inc(v_a_1638_);
lean_inc_ref(v_a_1637_);
lean_inc(v_a_1636_);
v___x_1665_ = lean_sym_simp(v_arg_1647_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_sub(v_i_1633_, v___x_1667_);
lean_dec(v_i_1633_);
v___x_1669_ = lean_nat_add(v_numEqs_1634_, v___x_1667_);
v___x_1670_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1635_, v_numEqs_1634_, v_a_1666_);
v_e_1632_ = v_fn_1646_;
v_i_1633_ = v___x_1668_;
v_numEqs_1634_ = v___x_1669_;
v_argResults_1635_ = v___x_1670_;
goto _start;
}
else
{
lean_dec_ref(v_fn_1646_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_argResults_1635_);
lean_dec(v_numEqs_1634_);
lean_dec(v_i_1633_);
lean_dec_ref(v_mkNonRflResult_1631_);
return v___x_1665_;
}
}
default: 
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec_ref(v_arg_1647_);
lean_dec_ref(v_fn_1646_);
lean_dec_ref(v_argResults_1635_);
lean_dec(v_numEqs_1634_);
lean_dec(v_i_1633_);
lean_dec_ref(v_mkNonRflResult_1631_);
v___x_1672_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1673_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1672_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
return v___x_1673_;
}
}
v___jp_1648_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_sub(v_i_1633_, v___x_1658_);
lean_dec(v_i_1633_);
v_e_1632_ = v_fn_1646_;
v_i_1633_ = v___x_1659_;
v_a_1636_ = v___y_1649_;
v_a_1637_ = v___y_1650_;
v_a_1638_ = v___y_1651_;
v_a_1639_ = v___y_1652_;
v_a_1640_ = v___y_1653_;
v_a_1641_ = v___y_1654_;
v_a_1642_ = v___y_1655_;
v_a_1643_ = v___y_1656_;
v_a_1644_ = v___y_1657_;
goto _start;
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
lean_dec(v_numEqs_1634_);
lean_dec(v_i_1633_);
lean_dec_ref(v_e_1632_);
v___x_1674_ = lean_array_get_size(v_argResults_1635_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_nat_dec_eq(v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = l_Array_reverse___redArg(v_argResults_1635_);
v___x_1678_ = lean_apply_11(v_mkNonRflResult_1631_, v___x_1677_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, lean_box(0));
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_argResults_1635_);
lean_dec_ref(v_mkNonRflResult_1631_);
v___x_1679_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object* v_argKinds_1681_, lean_object* v_mkNonRflResult_1682_, lean_object* v_e_1683_, lean_object* v_i_1684_, lean_object* v_numEqs_1685_, lean_object* v_argResults_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1681_, v_mkNonRflResult_1682_, v_e_1683_, v_i_1684_, v_numEqs_1685_, v_argResults_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec_ref(v_argKinds_1681_);
return v_res_1697_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_19921__overap_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
v___x_19921__overap_1711_ = lean_panic_fn(v___x_1710_, v_msg_1699_);
v___x_1712_ = lean_apply_10(v___x_19921__overap_1711_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, lean_box(0));
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* v_msg_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(uint8_t v___x_1725_, lean_object* v_as_1726_, size_t v_i_1727_, size_t v_stop_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_usize_dec_eq(v_i_1727_, v_stop_1728_);
if (v___x_1729_ == 0)
{
uint8_t v___x_1730_; uint8_t v___y_1732_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1730_ = 1;
v___x_1736_ = lean_array_uget_borrowed(v_as_1726_, v_i_1727_);
v___x_1737_ = lean_unbox(v___x_1736_);
if (v___x_1737_ == 3)
{
v___y_1732_ = v___x_1725_;
goto v___jp_1731_;
}
else
{
v___y_1732_ = v___x_1729_;
goto v___jp_1731_;
}
v___jp_1731_:
{
if (v___y_1732_ == 0)
{
size_t v___x_1733_; size_t v___x_1734_; 
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1727_, v___x_1733_);
v_i_1727_ = v___x_1734_;
goto _start;
}
else
{
return v___x_1730_;
}
}
}
else
{
uint8_t v___x_1738_; 
v___x_1738_ = 0;
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v___x_1739_, lean_object* v_as_1740_, lean_object* v_i_1741_, lean_object* v_stop_1742_){
_start:
{
uint8_t v___x_21628__boxed_1743_; size_t v_i_boxed_1744_; size_t v_stop_boxed_1745_; uint8_t v_res_1746_; lean_object* v_r_1747_; 
v___x_21628__boxed_1743_ = lean_unbox(v___x_1739_);
v_i_boxed_1744_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_stop_boxed_1745_ = lean_unbox_usize(v_stop_1742_);
lean_dec(v_stop_1742_);
v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v___x_21628__boxed_1743_, v_as_1740_, v_i_boxed_1744_, v_stop_boxed_1745_);
lean_dec_ref(v_as_1740_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1750_ = lean_unsigned_to_nat(13u);
v___x_1751_ = lean_unsigned_to_nat(391u);
v___x_1752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1753_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1754_ = l_mkPanicMessageWithDecl(v___x_1753_, v___x_1752_, v___x_1751_, v___x_1750_, v___x_1749_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1755_, lean_object* v_as_1756_, size_t v_sz_1757_, size_t v_i_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_a_1771_; uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_lt(v_i_1758_, v_sz_1757_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_b_1759_);
return v___x_1776_;
}
else
{
lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1971_; 
v_snd_1777_ = lean_ctor_get(v_b_1759_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_b_1759_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v_b_1759_, 0);
lean_dec(v_unused_1972_);
v___x_1779_ = v_b_1759_;
v_isShared_1780_ = v_isSharedCheck_1971_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_dec(v_b_1759_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1971_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_snd_1781_; lean_object* v_snd_1782_; lean_object* v_snd_1783_; lean_object* v_snd_1784_; lean_object* v_fst_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1969_; 
v_snd_1781_ = lean_ctor_get(v_snd_1777_, 1);
lean_inc(v_snd_1781_);
v_snd_1782_ = lean_ctor_get(v_snd_1781_, 1);
lean_inc(v_snd_1782_);
v_snd_1783_ = lean_ctor_get(v_snd_1782_, 1);
lean_inc(v_snd_1783_);
v_snd_1784_ = lean_ctor_get(v_snd_1783_, 1);
lean_inc(v_snd_1784_);
v_fst_1785_ = lean_ctor_get(v_snd_1777_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_snd_1777_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v_snd_1777_, 1);
lean_dec(v_unused_1970_);
v___x_1787_ = v_snd_1777_;
v_isShared_1788_ = v_isSharedCheck_1969_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_fst_1785_);
lean_dec(v_snd_1777_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1969_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_fst_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1967_; 
v_fst_1789_ = lean_ctor_get(v_snd_1781_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_snd_1781_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_snd_1781_, 1);
lean_dec(v_unused_1968_);
v___x_1791_ = v_snd_1781_;
v_isShared_1792_ = v_isSharedCheck_1967_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_fst_1789_);
lean_dec(v_snd_1781_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1967_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_fst_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1965_; 
v_fst_1793_ = lean_ctor_get(v_snd_1782_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_snd_1782_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v_snd_1782_, 1);
lean_dec(v_unused_1966_);
v___x_1795_ = v_snd_1782_;
v_isShared_1796_ = v_isSharedCheck_1965_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_fst_1793_);
lean_dec(v_snd_1782_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1965_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_fst_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1963_; 
v_fst_1797_ = lean_ctor_get(v_snd_1783_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_snd_1783_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_snd_1783_, 1);
lean_dec(v_unused_1964_);
v___x_1799_ = v_snd_1783_;
v_isShared_1800_ = v_isSharedCheck_1963_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_fst_1797_);
lean_dec(v_snd_1783_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1963_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_array_1801_; lean_object* v_start_1802_; lean_object* v_stop_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_array_1801_ = lean_ctor_get(v_snd_1784_, 0);
v_start_1802_ = lean_ctor_get(v_snd_1784_, 1);
v_stop_1803_ = lean_ctor_get(v_snd_1784_, 2);
v___x_1804_ = lean_box(0);
v___x_1805_ = lean_nat_dec_lt(v_start_1802_, v_stop_1803_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1807_; 
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
if (v_isShared_1800_ == 0)
{
v___x_1807_ = v___x_1799_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_snd_1784_);
v___x_1807_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v___x_1807_);
v___x_1809_ = v___x_1795_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_fst_1793_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1809_);
v___x_1811_ = v___x_1791_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_fst_1789_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1811_);
v___x_1813_ = v___x_1787_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_fst_1785_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v___x_1813_);
lean_ctor_set(v___x_1779_, 0, v___x_1804_);
v___x_1815_ = v___x_1779_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
}
}
}
else
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1959_; 
lean_inc(v_stop_1803_);
lean_inc(v_start_1802_);
lean_inc_ref(v_array_1801_);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_snd_1784_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; lean_object* v_unused_1961_; lean_object* v_unused_1962_; 
v_unused_1960_ = lean_ctor_get(v_snd_1784_, 2);
lean_dec(v_unused_1960_);
v_unused_1961_ = lean_ctor_get(v_snd_1784_, 1);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_snd_1784_, 0);
lean_dec(v_unused_1962_);
v___x_1823_ = v_snd_1784_;
v_isShared_1824_ = v_isSharedCheck_1959_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v_snd_1784_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1959_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v_a_1825_ = lean_array_uget_borrowed(v_as_1756_, v_i_1758_);
v___x_1826_ = lean_array_fget(v_array_1801_, v_start_1802_);
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = lean_nat_add(v_start_1802_, v___x_1827_);
lean_dec(v_start_1802_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1828_);
v___x_1830_ = v___x_1823_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_array_1801_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_stop_1803_);
v___x_1830_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_proof_1834_; lean_object* v_subst_1835_; uint8_t v___x_1861_; 
lean_inc(v_a_1825_);
v___x_1831_ = l_Lean_Expr_app___override(v_fst_1785_, v_a_1825_);
v___x_1832_ = l_Lean_Expr_bindingBody_x21(v_fst_1789_);
lean_dec(v_fst_1789_);
v___x_1861_ = lean_unbox(v___x_1826_);
lean_dec(v___x_1826_);
switch(v___x_1861_)
{
case 0:
{
lean_del_object(v___x_1799_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1787_);
lean_del_object(v___x_1779_);
goto v___jp_1854_;
}
case 3:
{
lean_del_object(v___x_1799_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1787_);
lean_del_object(v___x_1779_);
goto v___jp_1854_;
}
case 5:
{
lean_object* v___x_1862_; lean_object* v_instNew_1864_; lean_object* v___x_1873_; 
lean_del_object(v___x_1799_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1787_);
lean_del_object(v___x_1779_);
lean_inc(v_a_1825_);
v___x_1862_ = lean_array_push(v_fst_1797_, v_a_1825_);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
lean_inc(v_a_1825_);
v___x_1873_ = l_Lean_Meta_Sym_inferType___redArg(v_a_1825_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = l_Lean_Expr_bindingDomain_x21(v___x_1832_);
v___x_1876_ = lean_expr_instantiate_rev(v___x_1875_, v___x_1862_);
lean_dec_ref(v___x_1875_);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
lean_inc_ref(v___x_1876_);
v___x_1877_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_1874_, v___x_1876_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_unbox(v_a_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
v___x_1880_ = l_Lean_Meta_trySynthInstance(v___x_1876_, v___x_1804_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1897_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
if (lean_obj_tag(v_a_1881_) == 1)
{
lean_object* v_a_1885_; 
lean_del_object(v___x_1883_);
lean_dec(v_a_1878_);
v_a_1885_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v_a_1881_);
v_instNew_1864_ = v_a_1885_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v_a_1881_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v___x_1886_ = lean_alloc_ctor(0, 0, 1);
v___x_1887_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
lean_ctor_set_uint8(v___x_1886_, 0, v___x_1887_);
v___x_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1862_);
lean_ctor_set(v___x_1889_, 1, v___x_1830_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_fst_1793_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1832_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1831_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1888_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1893_);
v___x_1895_ = v___x_1883_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1878_);
lean_dec_ref(v___x_1862_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_dec(v_fst_1793_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v_a_1898_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1880_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1880_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_dec(v_a_1878_);
lean_dec_ref(v___x_1876_);
lean_inc(v_a_1825_);
v_instNew_1864_ = v_a_1825_;
goto v___jp_1863_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v___x_1876_);
lean_dec_ref(v___x_1862_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_dec(v_fst_1793_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v_a_1906_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1877_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1877_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___x_1862_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_dec(v_fst_1793_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v_a_1914_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1873_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1873_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
v___jp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_inc_ref(v_instNew_1864_);
v___x_1865_ = l_Lean_Expr_app___override(v___x_1831_, v_instNew_1864_);
v___x_1866_ = lean_array_push(v___x_1862_, v_instNew_1864_);
v___x_1867_ = l_Lean_Expr_bindingBody_x21(v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1830_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_fst_1793_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1867_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1865_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1804_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v_a_1771_ = v___x_1872_;
goto v___jp_1770_;
}
}
case 2:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1825_);
v___x_1923_ = lean_array_push(v_fst_1797_, v_a_1825_);
v___x_1924_ = lean_array_get_borrowed(v___x_1922_, v_argResults_1755_, v_fst_1793_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1925_; 
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
lean_inc(v_a_1825_);
v___x_1925_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_1825_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
lean_inc(v_a_1926_);
lean_inc(v_a_1825_);
v___x_1927_ = l_Lean_mkAppB(v___x_1831_, v_a_1825_, v_a_1926_);
lean_inc(v_a_1825_);
v___x_1928_ = lean_array_push(v___x_1923_, v_a_1825_);
v___x_1929_ = lean_array_push(v___x_1928_, v_a_1926_);
v_proof_1834_ = v___x_1927_;
v_subst_1835_ = v___x_1929_;
goto v___jp_1833_;
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v___x_1923_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_del_object(v___x_1799_);
lean_del_object(v___x_1795_);
lean_dec(v_fst_1793_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1787_);
lean_del_object(v___x_1779_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v_a_1930_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1925_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1925_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_e_x27_1938_; lean_object* v_proof_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_e_x27_1938_ = lean_ctor_get(v___x_1924_, 0);
v_proof_1939_ = lean_ctor_get(v___x_1924_, 1);
lean_inc_ref(v_proof_1939_);
lean_inc_ref(v_e_x27_1938_);
v___x_1940_ = l_Lean_mkAppB(v___x_1831_, v_e_x27_1938_, v_proof_1939_);
lean_inc_ref(v_e_x27_1938_);
v___x_1941_ = lean_array_push(v___x_1923_, v_e_x27_1938_);
lean_inc_ref(v_proof_1939_);
v___x_1942_ = lean_array_push(v___x_1941_, v_proof_1939_);
v_proof_1834_ = v___x_1940_;
v_subst_1835_ = v___x_1942_;
goto v___jp_1833_;
}
}
default: 
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_del_object(v___x_1799_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1787_);
lean_del_object(v___x_1779_);
v___x_1943_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
lean_inc(v___y_1760_);
v___x_1944_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_1943_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec_ref(v___x_1944_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_fst_1797_);
lean_ctor_set(v___x_1945_, 1, v___x_1830_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_fst_1793_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1832_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1831_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1804_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v_a_1771_ = v___x_1949_;
goto v___jp_1770_;
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_dec(v_fst_1797_);
lean_dec(v_fst_1793_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
v_a_1950_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1944_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1944_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
v___jp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1836_ = l_Lean_Expr_bindingBody_x21(v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1837_ = l_Lean_Expr_bindingBody_x21(v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = lean_nat_add(v_fst_1793_, v___x_1827_);
lean_dec(v_fst_1793_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1830_);
lean_ctor_set(v___x_1799_, 0, v_subst_1835_);
v___x_1840_ = v___x_1799_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_subst_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1830_);
v___x_1840_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v___x_1840_);
lean_ctor_set(v___x_1795_, 0, v___x_1838_);
v___x_1842_ = v___x_1795_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1842_);
lean_ctor_set(v___x_1791_, 0, v___x_1837_);
v___x_1844_ = v___x_1791_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1844_);
lean_ctor_set(v___x_1787_, 0, v_proof_1834_);
v___x_1846_ = v___x_1787_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_proof_1834_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v___x_1846_);
lean_ctor_set(v___x_1779_, 0, v___x_1804_);
v___x_1848_ = v___x_1779_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v_a_1771_ = v___x_1848_;
goto v___jp_1770_;
}
}
}
}
}
}
v___jp_1854_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_inc(v_a_1825_);
v___x_1855_ = lean_array_push(v_fst_1797_, v_a_1825_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1830_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_fst_1793_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1832_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1831_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1804_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v_a_1771_ = v___x_1860_;
goto v___jp_1770_;
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
v___jp_1770_:
{
size_t v___x_1772_; size_t v___x_1773_; 
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_add(v_i_1758_, v___x_1772_);
v_i_1758_ = v___x_1773_;
v_b_1759_ = v_a_1771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_1973_, lean_object* v_as_1974_, lean_object* v_sz_1975_, lean_object* v_i_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
size_t v_sz_boxed_1988_; size_t v_i_boxed_1989_; lean_object* v_res_1990_; 
v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1975_);
lean_dec(v_sz_1975_);
v_i_boxed_1989_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1973_, v_as_1974_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec_ref(v_as_1974_);
lean_dec_ref(v_argResults_1973_);
return v_res_1990_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1992_ = lean_unsigned_to_nat(34u);
v___x_1993_ = lean_unsigned_to_nat(392u);
v___x_1994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1996_ = l_mkPanicMessageWithDecl(v___x_1995_, v___x_1994_, v___x_1993_, v___x_1992_, v___x_1991_);
return v___x_1996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1999_; lean_object* v_dummy_2000_; 
v___x_1999_ = lean_box(0);
v_dummy_2000_ = l_Lean_Expr_sort___override(v___x_1999_);
return v_dummy_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_2004_, lean_object* v_argKinds_2005_, lean_object* v_type_2006_, lean_object* v_proof_2007_, lean_object* v_argResults_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v_j_2031_; lean_object* v_subst_2032_; lean_object* v_dummy_2033_; lean_object* v_nargs_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_args_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; size_t v_sz_2047_; size_t v___x_2048_; lean_object* v___x_2049_; 
v_j_2031_ = lean_unsigned_to_nat(0u);
v_subst_2032_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2033_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2034_ = l_Lean_Expr_getAppNumArgs(v_e_2004_);
lean_inc(v_nargs_2034_);
v___x_2035_ = lean_mk_array(v_nargs_2034_, v_dummy_2033_);
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = lean_nat_sub(v_nargs_2034_, v___x_2036_);
lean_dec(v_nargs_2034_);
v_args_2038_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2004_, v___x_2035_, v___x_2037_);
v___x_2039_ = lean_array_get_size(v_argKinds_2005_);
lean_inc_ref(v_argKinds_2005_);
v___x_2040_ = l_Array_toSubarray___redArg(v_argKinds_2005_, v_j_2031_, v___x_2039_);
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_subst_2032_);
lean_ctor_set(v___x_2042_, 1, v___x_2040_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_j_2031_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_type_2006_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_proof_2007_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v_sz_2047_ = lean_array_size(v_args_2038_);
v___x_2048_ = ((size_t)0ULL);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_2008_, v_args_2038_, v_sz_2047_, v___x_2048_, v___x_2046_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec_ref(v_args_2038_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2112_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2112_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2112_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_fst_2054_; 
v_fst_2054_ = lean_ctor_get(v_a_2050_, 0);
if (lean_obj_tag(v_fst_2054_) == 0)
{
lean_object* v_snd_2055_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v_rhs_2059_; lean_object* v___y_2060_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_del_object(v___x_2052_);
v_snd_2055_ = lean_ctor_get(v_a_2050_, 1);
lean_inc(v_snd_2055_);
lean_dec(v_a_2050_);
v_fst_2056_ = lean_ctor_get(v_snd_2055_, 0);
lean_inc(v_fst_2056_);
v_snd_2057_ = lean_ctor_get(v_snd_2055_, 1);
lean_inc(v_snd_2057_);
lean_dec(v_snd_2055_);
v_fst_2080_ = lean_ctor_get(v_snd_2057_, 0);
lean_inc(v_fst_2080_);
v_snd_2081_ = lean_ctor_get(v_snd_2057_, 1);
lean_inc(v_snd_2081_);
lean_dec(v_snd_2057_);
v___x_2082_ = l_Lean_Expr_cleanupAnnotations(v_fst_2080_);
v___x_2083_ = l_Lean_Expr_isApp(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v___x_2082_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2056_);
lean_dec_ref(v_argKinds_2005_);
v___y_2020_ = v___y_2009_;
v___y_2021_ = v___y_2010_;
v___y_2022_ = v___y_2011_;
v___y_2023_ = v___y_2012_;
v___y_2024_ = v___y_2013_;
v___y_2025_ = v___y_2014_;
v___y_2026_ = v___y_2015_;
v___y_2027_ = v___y_2016_;
v___y_2028_ = v___y_2017_;
goto v___jp_2019_;
}
else
{
lean_object* v_arg_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_arg_2084_ = lean_ctor_get(v___x_2082_, 1);
lean_inc_ref(v_arg_2084_);
v___x_2085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2082_);
v___x_2086_ = l_Lean_Expr_isApp(v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v___x_2085_);
lean_dec_ref(v_arg_2084_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2056_);
lean_dec_ref(v_argKinds_2005_);
v___y_2020_ = v___y_2009_;
v___y_2021_ = v___y_2010_;
v___y_2022_ = v___y_2011_;
v___y_2023_ = v___y_2012_;
v___y_2024_ = v___y_2013_;
v___y_2025_ = v___y_2014_;
v___y_2026_ = v___y_2015_;
v___y_2027_ = v___y_2016_;
v___y_2028_ = v___y_2017_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2085_);
v___x_2088_ = l_Lean_Expr_isApp(v___x_2087_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v___x_2087_);
lean_dec_ref(v_arg_2084_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2056_);
lean_dec_ref(v_argKinds_2005_);
v___y_2020_ = v___y_2009_;
v___y_2021_ = v___y_2010_;
v___y_2022_ = v___y_2011_;
v___y_2023_ = v___y_2012_;
v___y_2024_ = v___y_2013_;
v___y_2025_ = v___y_2014_;
v___y_2026_ = v___y_2015_;
v___y_2027_ = v___y_2016_;
v___y_2028_ = v___y_2017_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2087_);
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2091_ = l_Lean_Expr_isConstOf(v___x_2089_, v___x_2090_);
lean_dec_ref(v___x_2089_);
if (v___x_2091_ == 0)
{
lean_dec_ref(v_arg_2084_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2056_);
lean_dec_ref(v_argKinds_2005_);
v___y_2020_ = v___y_2009_;
v___y_2021_ = v___y_2010_;
v___y_2022_ = v___y_2011_;
v___y_2023_ = v___y_2012_;
v___y_2024_ = v___y_2013_;
v___y_2025_ = v___y_2014_;
v___y_2026_ = v___y_2015_;
v___y_2027_ = v___y_2016_;
v___y_2028_ = v___y_2017_;
goto v___jp_2019_;
}
else
{
lean_object* v_snd_2092_; lean_object* v_fst_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
v_snd_2092_ = lean_ctor_get(v_snd_2081_, 1);
lean_inc(v_snd_2092_);
lean_dec(v_snd_2081_);
v_fst_2093_ = lean_ctor_get(v_snd_2092_, 0);
lean_inc(v_fst_2093_);
lean_dec(v_snd_2092_);
v___x_2094_ = lean_expr_instantiate_rev(v_arg_2084_, v_fst_2093_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_arg_2084_);
v___x_2095_ = lean_nat_dec_lt(v_j_2031_, v___x_2039_);
if (v___x_2095_ == 0)
{
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v_argKinds_2005_);
v_rhs_2059_ = v___x_2094_;
v___y_2060_ = v___y_2013_;
goto v___jp_2058_;
}
else
{
if (v___x_2095_ == 0)
{
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v_argKinds_2005_);
v_rhs_2059_ = v___x_2094_;
v___y_2060_ = v___y_2013_;
goto v___jp_2058_;
}
else
{
size_t v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_usize_of_nat(v___x_2039_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v___x_2091_, v_argKinds_2005_, v___x_2048_, v___x_2096_);
lean_dec_ref(v_argKinds_2005_);
if (v___x_2097_ == 0)
{
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
v_rhs_2059_ = v___x_2094_;
v___y_2060_ = v___y_2013_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2094_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
v_rhs_2059_ = v_a_2099_;
v___y_2060_ = v___y_2013_;
goto v___jp_2058_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_fst_2056_);
lean_dec(v___y_2013_);
v_a_2100_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2098_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
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
v___jp_2058_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_rhs_2059_, v___y_2060_);
lean_dec(v___y_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2071_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2071_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2071_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2066_ = 0;
v___x_2067_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2067_, 0, v_a_2062_);
lean_ctor_set(v___x_2067_, 1, v_fst_2056_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*2, v___x_2066_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2067_);
v___x_2069_ = v___x_2064_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_fst_2056_);
v_a_2072_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2061_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2061_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v_val_2108_; lean_object* v___x_2110_; 
lean_inc_ref(v_fst_2054_);
lean_dec(v_a_2050_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v_argKinds_2005_);
v_val_2108_ = lean_ctor_get(v_fst_2054_, 0);
lean_inc(v_val_2108_);
lean_dec_ref(v_fst_2054_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v_val_2108_);
v___x_2110_ = v___x_2052_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_val_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v_argKinds_2005_);
v_a_2113_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2049_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2049_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
v___jp_2019_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_2030_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2029_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2121_, lean_object* v_argKinds_2122_, lean_object* v_type_2123_, lean_object* v_proof_2124_, lean_object* v_argResults_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2121_, v_argKinds_2122_, v_type_2123_, v_proof_2124_, v_argResults_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec_ref(v_argResults_2125_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2149_, 0, v___x_2137_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2151_, lean_object* v_x_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___x_22319__boxed_2163_; lean_object* v_res_2164_; 
v___x_22319__boxed_2163_ = lean_unbox(v___x_2151_);
v_res_2164_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_22319__boxed_2163_, v_x_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v_x_2152_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2167_, lean_object* v_argKinds_2168_, lean_object* v_mkNonRflResult_2169_, lean_object* v_x_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_sub(v___x_2167_, v___x_2181_);
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2185_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2168_, v_mkNonRflResult_2169_, v_x_2170_, v___x_2182_, v___x_2183_, v___x_2184_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2186_, lean_object* v_argKinds_2187_, lean_object* v_mkNonRflResult_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2186_, v_argKinds_2187_, v_mkNonRflResult_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec_ref(v_argKinds_2187_);
lean_dec(v___x_2186_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2201_, lean_object* v_thm_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_type_2213_; lean_object* v_proof_2214_; lean_object* v_argKinds_2215_; lean_object* v_mkNonRflResult_2216_; lean_object* v_numArgs_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v_type_2213_ = lean_ctor_get(v_thm_2202_, 0);
lean_inc_ref(v_type_2213_);
v_proof_2214_ = lean_ctor_get(v_thm_2202_, 1);
lean_inc_ref(v_proof_2214_);
v_argKinds_2215_ = lean_ctor_get(v_thm_2202_, 2);
lean_inc_ref(v_argKinds_2215_);
lean_dec_ref(v_thm_2202_);
lean_inc_ref(v_argKinds_2215_);
lean_inc_ref(v_e_2201_);
v_mkNonRflResult_2216_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2216_, 0, v_e_2201_);
lean_closure_set(v_mkNonRflResult_2216_, 1, v_argKinds_2215_);
lean_closure_set(v_mkNonRflResult_2216_, 2, v_type_2213_);
lean_closure_set(v_mkNonRflResult_2216_, 3, v_proof_2214_);
v_numArgs_2217_ = l_Lean_Expr_getAppNumArgs(v_e_2201_);
v___x_2218_ = lean_array_get_size(v_argKinds_2215_);
v___x_2219_ = lean_nat_dec_lt(v___x_2218_, v_numArgs_2217_);
if (v___x_2219_ == 0)
{
uint8_t v___x_2220_; 
v___x_2220_ = lean_nat_dec_lt(v_numArgs_2217_, v___x_2218_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_numArgs_2217_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_nat_sub(v___x_2218_, v___x_2221_);
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2225_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2215_, v_mkNonRflResult_2216_, v_e_2201_, v___x_2222_, v___x_2223_, v___x_2224_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec_ref(v_argKinds_2215_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_mkNonRflResult_2216_);
lean_dec_ref(v_argKinds_2215_);
v___x_2226_ = lean_box(v___x_2219_);
v___f_2227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2227_, 0, v___x_2226_);
v___x_2228_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2227_, v_e_2201_, v_numArgs_2217_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec(v_numArgs_2217_);
return v___x_2228_;
}
}
else
{
lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___f_2229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2229_, 0, v___x_2218_);
lean_closure_set(v___f_2229_, 1, v_argKinds_2215_);
lean_closure_set(v___f_2229_, 2, v_mkNonRflResult_2216_);
v___x_2230_ = lean_nat_sub(v_numArgs_2217_, v___x_2218_);
lean_dec(v_numArgs_2217_);
v___x_2231_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2229_, v_e_2201_, v___x_2230_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec(v___x_2230_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2232_, lean_object* v_thm_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2232_, v_thm_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_f_2256_; lean_object* v___x_2257_; 
v_f_2256_ = l_Lean_Expr_getAppFn(v_e_2245_);
lean_inc(v_a_2254_);
lean_inc_ref(v_a_2253_);
lean_inc(v_a_2252_);
lean_inc_ref(v_a_2251_);
v___x_2257_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2256_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2273_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2273_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2273_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
switch(lean_obj_tag(v_a_2258_))
{
case 0:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_e_2245_);
v___x_2262_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
case 1:
{
lean_object* v_prefixSize_2266_; lean_object* v_suffixSize_2267_; lean_object* v___x_2268_; 
lean_del_object(v___x_2260_);
v_prefixSize_2266_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_prefixSize_2266_);
v_suffixSize_2267_ = lean_ctor_get(v_a_2258_, 1);
lean_inc(v_suffixSize_2267_);
lean_dec_ref(v_a_2258_);
v___x_2268_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2245_, v_prefixSize_2266_, v_suffixSize_2267_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_prefixSize_2266_);
return v___x_2268_;
}
case 2:
{
lean_object* v_rewritable_2269_; lean_object* v___x_2270_; 
lean_del_object(v___x_2260_);
v_rewritable_2269_ = lean_ctor_get(v_a_2258_, 0);
lean_inc_ref(v_rewritable_2269_);
lean_dec_ref(v_a_2258_);
v___x_2270_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2245_, v_rewritable_2269_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
return v___x_2270_;
}
default: 
{
lean_object* v_thm_2271_; lean_object* v___x_2272_; 
lean_del_object(v___x_2260_);
v_thm_2271_ = lean_ctor_get(v_a_2258_, 0);
lean_inc_ref(v_thm_2271_);
lean_dec_ref(v_a_2258_);
v___x_2272_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2245_, v_thm_2271_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_e_2245_);
v_a_2274_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2257_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2257_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
return v_res_2293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2296_ = lean_unsigned_to_nat(55u);
v___x_2297_ = lean_unsigned_to_nat(469u);
v___x_2298_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2299_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2300_ = l_mkPanicMessageWithDecl(v___x_2299_, v___x_2298_, v___x_2297_, v___x_2296_, v___x_2295_);
return v___x_2300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2302_ = lean_unsigned_to_nat(11u);
v___x_2303_ = lean_unsigned_to_nat(477u);
v___x_2304_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2305_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2306_ = l_mkPanicMessageWithDecl(v___x_2305_, v___x_2304_, v___x_2303_, v___x_2302_, v___x_2301_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2307_, lean_object* v_e_2308_, lean_object* v_i_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = lean_nat_dec_eq(v_i_2309_, v___x_2320_);
if (v___x_2321_ == 0)
{
if (lean_obj_tag(v_e_2308_) == 5)
{
lean_object* v_fn_2325_; lean_object* v_arg_2326_; lean_object* v___x_2327_; lean_object* v_i_2328_; lean_object* v___x_2329_; 
v_fn_2325_ = lean_ctor_get(v_e_2308_, 0);
lean_inc_ref(v_fn_2325_);
v_arg_2326_ = lean_ctor_get(v_e_2308_, 1);
lean_inc_ref(v_arg_2326_);
v___x_2327_ = lean_unsigned_to_nat(1u);
v_i_2328_ = lean_nat_sub(v_i_2309_, v___x_2327_);
lean_inc(v_a_2318_);
lean_inc_ref(v_a_2317_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
lean_inc(v_a_2312_);
lean_inc_ref(v_a_2311_);
lean_inc(v_a_2310_);
lean_inc_ref(v_fn_2325_);
v___x_2329_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2307_, v_fn_2325_, v_i_2328_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = lean_nat_dec_lt(v_i_2328_, v_stop_2307_);
lean_dec(v_i_2328_);
if (v___x_2331_ == 0)
{
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
if (lean_obj_tag(v_a_2330_) == 0)
{
lean_dec_ref(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
goto v___jp_2322_;
}
else
{
lean_object* v_e_x27_2332_; lean_object* v_proof_2333_; lean_object* v___x_2334_; 
v_e_x27_2332_ = lean_ctor_get(v_a_2330_, 0);
lean_inc_ref(v_e_x27_2332_);
v_proof_2333_ = lean_ctor_get(v_a_2330_, 1);
lean_inc_ref(v_proof_2333_);
lean_dec_ref(v_a_2330_);
v___x_2334_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2308_, v_fn_2325_, v_arg_2326_, v_e_x27_2332_, v_proof_2333_, v___x_2321_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2334_;
}
}
else
{
lean_object* v___x_2335_; 
lean_inc(v_a_2318_);
lean_inc_ref(v_a_2317_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc_ref(v_fn_2325_);
v___x_2335_ = l_Lean_Meta_Sym_inferType___redArg(v_fn_2325_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
lean_inc(v_a_2318_);
lean_inc_ref(v_a_2317_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
v___x_2337_ = l_Lean_Meta_whnfD(v_a_2336_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
if (lean_obj_tag(v_a_2338_) == 7)
{
lean_object* v_binderType_2339_; lean_object* v_body_2340_; uint8_t v___x_2358_; 
v_binderType_2339_ = lean_ctor_get(v_a_2338_, 1);
lean_inc_ref(v_binderType_2339_);
v_body_2340_ = lean_ctor_get(v_a_2338_, 2);
lean_inc_ref(v_body_2340_);
lean_dec_ref(v_a_2338_);
v___x_2358_ = l_Lean_Expr_hasLooseBVars(v_body_2340_);
lean_dec_ref(v_body_2340_);
if (v___x_2358_ == 0)
{
goto v___jp_2341_;
}
else
{
if (v___x_2321_ == 0)
{
lean_dec_ref(v_binderType_2339_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
if (lean_obj_tag(v_a_2330_) == 0)
{
lean_dec_ref(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
goto v___jp_2322_;
}
else
{
lean_object* v_e_x27_2359_; lean_object* v_proof_2360_; lean_object* v___x_2361_; 
v_e_x27_2359_ = lean_ctor_get(v_a_2330_, 0);
lean_inc_ref(v_e_x27_2359_);
v_proof_2360_ = lean_ctor_get(v_a_2330_, 1);
lean_inc_ref(v_proof_2360_);
lean_dec_ref(v_a_2330_);
v___x_2361_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2308_, v_fn_2325_, v_arg_2326_, v_e_x27_2359_, v_proof_2360_, v___x_2321_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2361_;
}
}
else
{
goto v___jp_2341_;
}
}
v___jp_2341_:
{
lean_object* v___x_2342_; 
lean_inc(v_a_2318_);
lean_inc_ref(v_a_2317_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
v___x_2342_ = l_Lean_Meta_isProp(v_binderType_2339_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_inc(v_a_2318_);
lean_inc_ref(v_a_2317_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
lean_inc_ref(v_arg_2326_);
v___x_2345_ = lean_sym_simp(v_arg_2326_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2308_, v_fn_2325_, v_arg_2326_, v_a_2330_, v_a_2346_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2347_;
}
else
{
lean_dec(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_e_2308_);
lean_dec_ref(v_fn_2325_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v___x_2345_;
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
v___x_2348_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2348_, 0, v___x_2321_);
v___x_2349_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2308_, v_fn_2325_, v_arg_2326_, v_a_2330_, v___x_2348_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2349_;
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
v_a_2350_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2342_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2342_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec(v_a_2338_);
lean_dec(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2363_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2362_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2363_;
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
v_a_2364_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2337_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2337_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2330_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
v_a_2372_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2335_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2335_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
else
{
lean_dec(v_i_2328_);
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_fn_2325_);
lean_dec_ref(v_e_2308_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
return v___x_2329_;
}
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec_ref(v_e_2308_);
v___x_2380_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2381_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2380_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2381_;
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_e_2308_);
v___x_2382_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
v___jp_2322_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2323_, 0, v___x_2321_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2384_, lean_object* v_e_2385_, lean_object* v_i_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2384_, v_e_2385_, v_i_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_i_2386_);
lean_dec(v_stop_2384_);
return v_res_2397_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2400_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2401_ = lean_unsigned_to_nat(2u);
v___x_2402_ = lean_unsigned_to_nat(453u);
v___x_2403_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2404_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2405_ = l_mkPanicMessageWithDecl(v___x_2404_, v___x_2403_, v___x_2402_, v___x_2401_, v___x_2400_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2406_, lean_object* v_start_2407_, lean_object* v_stop_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_nat_dec_lt(v_start_2407_, v_stop_2408_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec_ref(v_e_2406_);
v___x_2420_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2421_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2420_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2421_;
}
else
{
lean_object* v_numArgs_2422_; uint8_t v___x_2423_; 
v_numArgs_2422_ = l_Lean_Expr_getAppNumArgs(v_e_2406_);
v___x_2423_ = lean_nat_dec_lt(v_numArgs_2422_, v_start_2407_);
if (v___x_2423_ == 0)
{
lean_object* v_numArgs_2424_; lean_object* v_stop_2425_; lean_object* v___x_2426_; 
v_numArgs_2424_ = lean_nat_sub(v_numArgs_2422_, v_start_2407_);
lean_dec(v_numArgs_2422_);
v_stop_2425_ = lean_nat_sub(v_stop_2408_, v_start_2407_);
v___x_2426_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2425_, v_e_2406_, v_numArgs_2424_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_numArgs_2424_);
lean_dec(v_stop_2425_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v_numArgs_2422_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_e_2406_);
v___x_2427_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2429_, lean_object* v_start_2430_, lean_object* v_stop_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2429_, v_start_2430_, v_stop_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_stop_2431_);
lean_dec(v_start_2430_);
return v_res_2442_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_App(builtin);
}
#ifdef __cplusplus
}
#endif
