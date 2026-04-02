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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congrFun'"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 239, 156, 219, 118, 185, 235, 192)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object**);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*10);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
lean_inc_ref(v_f_1_);
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v___x_16_);
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
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object* v_f_34_, lean_object* v_a_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_34_, v_a_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object* v_a_44_, lean_object* v_e_45_, lean_object* v_declName_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_Sym_inferType___redArg(v_a_44_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_n(v_a_55_, 2);
lean_dec_ref(v___x_54_);
v___x_56_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_55_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
lean_dec_ref(v___x_56_);
v___x_58_ = l_Lean_Meta_Sym_inferType___redArg(v_e_45_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc_n(v_a_59_, 2);
lean_dec_ref(v___x_58_);
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
lean_dec(v_declName_46_);
return v___x_58_;
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec(v_a_55_);
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
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object* v_e_110_, lean_object* v_f_111_, lean_object* v_a_112_, lean_object* v_fr_113_, lean_object* v_ar_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
uint8_t v___y_123_; 
if (lean_obj_tag(v_fr_113_) == 0)
{
if (lean_obj_tag(v_ar_114_) == 0)
{
uint8_t v_contextDependent_126_; 
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
lean_dec_ref(v_e_110_);
v_contextDependent_126_ = lean_ctor_get_uint8(v_fr_113_, 1);
lean_dec_ref(v_fr_113_);
if (v_contextDependent_126_ == 0)
{
uint8_t v_contextDependent_127_; 
v_contextDependent_127_ = lean_ctor_get_uint8(v_ar_114_, 1);
lean_dec_ref(v_ar_114_);
v___y_123_ = v_contextDependent_127_;
goto v___jp_122_;
}
else
{
lean_dec_ref(v_ar_114_);
v___y_123_ = v_contextDependent_126_;
goto v___jp_122_;
}
}
else
{
uint8_t v_contextDependent_128_; lean_object* v_e_x27_129_; lean_object* v_proof_130_; uint8_t v_contextDependent_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_170_; 
v_contextDependent_128_ = lean_ctor_get_uint8(v_fr_113_, 1);
lean_dec_ref(v_fr_113_);
v_e_x27_129_ = lean_ctor_get(v_ar_114_, 0);
v_proof_130_ = lean_ctor_get(v_ar_114_, 1);
v_contextDependent_131_ = lean_ctor_get_uint8(v_ar_114_, sizeof(void*)*2 + 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_ar_114_);
if (v_isSharedCheck_170_ == 0)
{
v___x_133_ = v_ar_114_;
v_isShared_134_ = v_isSharedCheck_170_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_proof_130_);
lean_inc(v_e_x27_129_);
lean_dec(v_ar_114_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_170_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; 
lean_inc_ref(v_e_x27_129_);
lean_inc_ref(v_f_111_);
v___x_135_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_111_, v_e_x27_129_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref(v___x_135_);
v___x_137_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
lean_inc_ref(v_a_112_);
v___x_138_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_112_, v_e_110_, v___x_137_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_153_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_153_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_153_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_153_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; uint8_t v___x_144_; uint8_t v___y_146_; 
v___x_143_ = l_Lean_mkApp4(v_a_139_, v_a_112_, v_e_x27_129_, v_f_111_, v_proof_130_);
v___x_144_ = 0;
if (v_contextDependent_128_ == 0)
{
v___y_146_ = v_contextDependent_131_;
goto v___jp_145_;
}
else
{
v___y_146_ = v_contextDependent_128_;
goto v___jp_145_;
}
v___jp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_143_);
lean_ctor_set(v___x_133_, 0, v_a_136_);
v___x_148_ = v___x_133_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_136_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_143_);
v___x_148_ = v_reuseFailAlloc_152_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*2, v___x_144_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*2 + 1, v___y_146_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_148_);
v___x_150_ = v___x_141_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_a_136_);
lean_del_object(v___x_133_);
lean_dec_ref(v_proof_130_);
lean_dec_ref(v_e_x27_129_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
v_a_154_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_138_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_138_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_del_object(v___x_133_);
lean_dec_ref(v_proof_130_);
lean_dec_ref(v_e_x27_129_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
lean_dec_ref(v_e_110_);
v_a_162_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_135_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_135_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_ar_114_) == 0)
{
lean_object* v_e_x27_171_; lean_object* v_proof_172_; uint8_t v_contextDependent_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_213_; 
v_e_x27_171_ = lean_ctor_get(v_fr_113_, 0);
v_proof_172_ = lean_ctor_get(v_fr_113_, 1);
v_contextDependent_173_ = lean_ctor_get_uint8(v_fr_113_, sizeof(void*)*2 + 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_fr_113_);
if (v_isSharedCheck_213_ == 0)
{
v___x_175_ = v_fr_113_;
v_isShared_176_ = v_isSharedCheck_213_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_proof_172_);
lean_inc(v_e_x27_171_);
lean_dec(v_fr_113_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_213_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint8_t v_contextDependent_177_; lean_object* v___x_178_; 
v_contextDependent_177_ = lean_ctor_get_uint8(v_ar_114_, 1);
lean_dec_ref(v_ar_114_);
lean_inc_ref(v_a_112_);
lean_inc_ref(v_e_x27_171_);
v___x_178_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_171_, v_a_112_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref(v___x_178_);
v___x_180_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
lean_inc_ref(v_a_112_);
v___x_181_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_112_, v_e_110_, v___x_180_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_196_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_196_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; uint8_t v___x_187_; uint8_t v___y_189_; 
v___x_186_ = l_Lean_mkApp4(v_a_182_, v_f_111_, v_e_x27_171_, v_proof_172_, v_a_112_);
v___x_187_ = 0;
if (v_contextDependent_173_ == 0)
{
v___y_189_ = v_contextDependent_177_;
goto v___jp_188_;
}
else
{
v___y_189_ = v_contextDependent_173_;
goto v___jp_188_;
}
v___jp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_186_);
lean_ctor_set(v___x_175_, 0, v_a_179_);
v___x_191_ = v___x_175_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_179_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_186_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*2, v___x_187_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*2 + 1, v___y_189_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_191_);
v___x_193_ = v___x_184_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_a_179_);
lean_del_object(v___x_175_);
lean_dec_ref(v_proof_172_);
lean_dec_ref(v_e_x27_171_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
v_a_197_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_181_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_181_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_del_object(v___x_175_);
lean_dec_ref(v_proof_172_);
lean_dec_ref(v_e_x27_171_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
lean_dec_ref(v_e_110_);
v_a_205_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_178_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_178_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
else
{
lean_object* v_e_x27_214_; lean_object* v_proof_215_; uint8_t v_contextDependent_216_; lean_object* v_e_x27_217_; lean_object* v_proof_218_; uint8_t v_contextDependent_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_258_; 
v_e_x27_214_ = lean_ctor_get(v_fr_113_, 0);
lean_inc_ref(v_e_x27_214_);
v_proof_215_ = lean_ctor_get(v_fr_113_, 1);
lean_inc_ref(v_proof_215_);
v_contextDependent_216_ = lean_ctor_get_uint8(v_fr_113_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fr_113_);
v_e_x27_217_ = lean_ctor_get(v_ar_114_, 0);
v_proof_218_ = lean_ctor_get(v_ar_114_, 1);
v_contextDependent_219_ = lean_ctor_get_uint8(v_ar_114_, sizeof(void*)*2 + 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_ar_114_);
if (v_isSharedCheck_258_ == 0)
{
v___x_221_ = v_ar_114_;
v_isShared_222_ = v_isSharedCheck_258_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_proof_218_);
lean_inc(v_e_x27_217_);
lean_dec(v_ar_114_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_258_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; 
lean_inc_ref(v_e_x27_217_);
lean_inc_ref(v_e_x27_214_);
v___x_223_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_214_, v_e_x27_217_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref(v___x_223_);
v___x_225_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
lean_inc_ref(v_a_112_);
v___x_226_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_112_, v_e_110_, v___x_225_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_241_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; uint8_t v___x_232_; uint8_t v___y_234_; 
v___x_231_ = l_Lean_mkApp6(v_a_227_, v_f_111_, v_e_x27_214_, v_a_112_, v_e_x27_217_, v_proof_215_, v_proof_218_);
v___x_232_ = 0;
if (v_contextDependent_216_ == 0)
{
v___y_234_ = v_contextDependent_219_;
goto v___jp_233_;
}
else
{
v___y_234_ = v_contextDependent_216_;
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_231_);
lean_ctor_set(v___x_221_, 0, v_a_224_);
v___x_236_ = v___x_221_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_224_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_231_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*2, v___x_232_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*2 + 1, v___y_234_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_236_);
v___x_238_ = v___x_229_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_a_224_);
lean_del_object(v___x_221_);
lean_dec_ref(v_proof_218_);
lean_dec_ref(v_e_x27_217_);
lean_dec_ref(v_proof_215_);
lean_dec_ref(v_e_x27_214_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
v_a_242_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_226_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_226_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_del_object(v___x_221_);
lean_dec_ref(v_proof_218_);
lean_dec_ref(v_e_x27_217_);
lean_dec_ref(v_proof_215_);
lean_dec_ref(v_e_x27_214_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_f_111_);
lean_dec_ref(v_e_110_);
v_a_250_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_223_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_223_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_123_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object* v_e_259_, lean_object* v_f_260_, lean_object* v_a_261_, lean_object* v_fr_262_, lean_object* v_ar_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_259_, v_f_260_, v_a_261_, v_fr_262_, v_ar_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object* v_e_272_, lean_object* v_f_273_, lean_object* v_a_274_, lean_object* v_fr_275_, lean_object* v_ar_276_, lean_object* v_x_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_272_, v_f_273_, v_a_274_, v_fr_275_, v_ar_276_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object* v_e_286_, lean_object* v_f_287_, lean_object* v_a_288_, lean_object* v_fr_289_, lean_object* v_ar_290_, lean_object* v_x_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Sym_Simp_mkCongr(v_e_286_, v_f_287_, v_a_288_, v_fr_289_, v_ar_290_, v_x_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_mctx_309_; lean_object* v_lctx_310_; lean_object* v_options_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_302_);
v_mctx_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_309_);
lean_dec(v___x_308_);
v_lctx_310_ = lean_ctor_get(v___y_301_, 2);
v_options_311_ = lean_ctor_get(v___y_303_, 2);
lean_inc_ref(v_options_311_);
lean_inc_ref(v_lctx_310_);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_env_307_);
lean_ctor_set(v___x_312_, 1, v_mctx_309_);
lean_ctor_set(v___x_312_, 2, v_lctx_310_);
lean_ctor_set(v___x_312_, 3, v_options_311_);
v___x_313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_msgData_300_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* v_msg_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_ref_328_; lean_object* v___x_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_ref_328_ = lean_ctor_get(v___y_325_, 5);
v___x_329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msg_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
lean_inc(v_ref_328_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_ref_328_);
lean_ctor_set(v___x_334_, 1, v_a_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* v_e_352_, lean_object* v_f_353_, lean_object* v_a_354_, lean_object* v_f_x27_355_, lean_object* v_hf_356_, uint8_t v_done_357_, uint8_t v_contextDependent_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; 
lean_inc_ref(v_f_353_);
v___x_366_ = l_Lean_Meta_Sym_inferType___redArg(v_f_353_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_366_);
v___x_368_ = l_Lean_Meta_whnfD(v_a_367_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
if (lean_obj_tag(v_a_369_) == 7)
{
lean_object* v_binderName_370_; lean_object* v_body_371_; lean_object* v___x_372_; 
v_binderName_370_ = lean_ctor_get(v_a_369_, 0);
lean_inc(v_binderName_370_);
v_body_371_ = lean_ctor_get(v_a_369_, 2);
lean_inc_ref(v_body_371_);
lean_dec_ref(v_a_369_);
lean_inc_ref(v_a_354_);
v___x_372_ = l_Lean_Meta_Sym_inferType___redArg(v_a_354_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_n(v_a_373_, 2);
lean_dec_ref(v___x_372_);
v___x_374_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_373_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref(v___x_374_);
v___x_376_ = l_Lean_Meta_Sym_inferType___redArg(v_e_352_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_376_);
v___x_378_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
lean_inc_ref(v_a_354_);
lean_inc_ref(v_f_x27_355_);
v___x_380_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_x27_355_, v_a_354_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_397_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_397_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_397_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_385_ = 0;
lean_inc(v_a_373_);
v___x_386_ = l_Lean_mkLambda(v_binderName_370_, v___x_385_, v_a_373_, v_body_371_);
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_a_379_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v_a_375_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_mkConst(v___x_387_, v___x_390_);
v___x_392_ = l_Lean_mkApp6(v___x_391_, v_a_373_, v___x_386_, v_f_353_, v_f_x27_355_, v_hf_356_, v_a_354_);
v___x_393_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_393_, 0, v_a_381_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*2, v_done_357_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*2 + 1, v_contextDependent_358_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_393_);
v___x_395_ = v___x_383_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_a_379_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_dec_ref(v_body_371_);
lean_dec(v_binderName_370_);
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
v_a_398_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_380_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_380_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_dec_ref(v_body_371_);
lean_dec(v_binderName_370_);
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
v_a_406_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_378_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_378_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_dec_ref(v_body_371_);
lean_dec(v_binderName_370_);
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
v_a_414_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_376_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_376_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_373_);
lean_dec_ref(v_body_371_);
lean_dec(v_binderName_370_);
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
lean_dec_ref(v_e_352_);
v_a_422_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_374_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_374_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_body_371_);
lean_dec(v_binderName_370_);
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
lean_dec_ref(v_e_352_);
v_a_430_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_372_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_372_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
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
else
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_a_369_);
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_e_352_);
v___x_438_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
v___x_439_ = l_Lean_indentExpr(v_f_353_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_440_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
return v___x_441_;
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
lean_dec_ref(v_e_352_);
v_a_442_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_368_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_368_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v_hf_356_);
lean_dec_ref(v_f_x27_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_f_353_);
lean_dec_ref(v_e_352_);
v_a_450_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_366_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_366_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* v_e_458_, lean_object* v_f_459_, lean_object* v_a_460_, lean_object* v_f_x27_461_, lean_object* v_hf_462_, lean_object* v_done_463_, lean_object* v_contextDependent_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
uint8_t v_done_boxed_472_; uint8_t v_contextDependent_boxed_473_; lean_object* v_res_474_; 
v_done_boxed_472_ = lean_unbox(v_done_463_);
v_contextDependent_boxed_473_ = lean_unbox(v_contextDependent_464_);
v_res_474_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_458_, v_f_459_, v_a_460_, v_f_x27_461_, v_hf_462_, v_done_boxed_472_, v_contextDependent_boxed_473_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* v_e_475_, lean_object* v_f_476_, lean_object* v_a_477_, lean_object* v_f_x27_478_, lean_object* v_hf_479_, lean_object* v_x_480_, uint8_t v_done_481_, uint8_t v_contextDependent_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_475_, v_f_476_, v_a_477_, v_f_x27_478_, v_hf_479_, v_done_481_, v_contextDependent_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* v_e_491_, lean_object* v_f_492_, lean_object* v_a_493_, lean_object* v_f_x27_494_, lean_object* v_hf_495_, lean_object* v_x_496_, lean_object* v_done_497_, lean_object* v_contextDependent_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
uint8_t v_done_boxed_506_; uint8_t v_contextDependent_boxed_507_; lean_object* v_res_508_; 
v_done_boxed_506_ = lean_unbox(v_done_497_);
v_contextDependent_boxed_507_ = lean_unbox(v_contextDependent_498_);
v_res_508_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(v_e_491_, v_f_492_, v_a_493_, v_f_x27_494_, v_hf_495_, v_x_496_, v_done_boxed_506_, v_contextDependent_boxed_507_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* v_00_u03b1_509_, lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_510_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* v_00_u03b1_519_, lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(v_00_u03b1_519_, v_msg_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_528_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* v_msg_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_9179__overap_542_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_9179__overap_542_ = lean_panic_fn_borrowed(v___x_541_, v_msg_530_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc(v___y_537_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
v___x_543_ = lean_apply_10(v___x_9179__overap_542_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, lean_box(0));
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
return v_res_555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_560_ = lean_unsigned_to_nat(55u);
v___x_561_ = lean_unsigned_to_nat(123u);
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_563_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_564_ = l_mkPanicMessageWithDecl(v___x_563_, v___x_562_, v___x_561_, v___x_560_, v___x_559_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_565_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_566_ = lean_unsigned_to_nat(13u);
v___x_567_ = lean_unsigned_to_nat(135u);
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_569_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_570_ = l_mkPanicMessageWithDecl(v___x_569_, v___x_568_, v___x_567_, v___x_566_, v___x_565_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* v_simpFn_571_, lean_object* v_e_572_, lean_object* v_i_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_nat_dec_eq(v_i_573_, v___x_584_);
if (v___x_585_ == 0)
{
if (lean_obj_tag(v_e_572_) == 5)
{
lean_object* v_fn_586_; lean_object* v_arg_587_; lean_object* v___x_588_; lean_object* v_i_589_; lean_object* v___x_590_; 
v_fn_586_ = lean_ctor_get(v_e_572_, 0);
lean_inc_ref_n(v_fn_586_, 2);
v_arg_587_ = lean_ctor_get(v_e_572_, 1);
lean_inc_ref(v_arg_587_);
v___x_588_ = lean_unsigned_to_nat(1u);
v_i_589_ = lean_nat_sub(v_i_573_, v___x_588_);
v___x_590_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_571_, v_fn_586_, v_i_589_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_i_589_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_590_);
lean_inc_ref(v_fn_586_);
v___x_592_ = l_Lean_Meta_Sym_inferType___redArg(v_fn_586_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v___x_594_ = l_Lean_Meta_whnfD(v_a_593_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_630_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_630_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_630_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_630_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
if (lean_obj_tag(v_a_595_) == 7)
{
lean_object* v_binderType_599_; lean_object* v_body_600_; uint8_t v___x_618_; 
v_binderType_599_ = lean_ctor_get(v_a_595_, 1);
lean_inc_ref(v_binderType_599_);
v_body_600_ = lean_ctor_get(v_a_595_, 2);
lean_inc_ref(v_body_600_);
lean_dec_ref(v_a_595_);
v___x_618_ = l_Lean_Expr_hasLooseBVars(v_body_600_);
lean_dec_ref(v_body_600_);
if (v___x_618_ == 0)
{
lean_del_object(v___x_597_);
goto v___jp_601_;
}
else
{
if (v___x_585_ == 0)
{
lean_dec_ref(v_binderType_599_);
if (lean_obj_tag(v_a_591_) == 0)
{
uint8_t v_contextDependent_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
v_contextDependent_619_ = lean_ctor_get_uint8(v_a_591_, 1);
lean_dec_ref(v_a_591_);
v___x_620_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_619_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_620_);
v___x_622_ = v___x_597_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v_e_x27_624_; lean_object* v_proof_625_; uint8_t v_contextDependent_626_; lean_object* v___x_627_; 
lean_del_object(v___x_597_);
v_e_x27_624_ = lean_ctor_get(v_a_591_, 0);
lean_inc_ref(v_e_x27_624_);
v_proof_625_ = lean_ctor_get(v_a_591_, 1);
lean_inc_ref(v_proof_625_);
v_contextDependent_626_ = lean_ctor_get_uint8(v_a_591_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_591_);
v___x_627_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_572_, v_fn_586_, v_arg_587_, v_e_x27_624_, v_proof_625_, v___x_585_, v_contextDependent_626_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_627_;
}
}
else
{
lean_del_object(v___x_597_);
goto v___jp_601_;
}
}
v___jp_601_:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_isProp(v_binderType_599_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; uint8_t v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
v___x_604_ = lean_unbox(v_a_603_);
lean_dec(v_a_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_inc(v_a_582_);
lean_inc_ref(v_a_581_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_arg_587_);
v___x_605_ = lean_sym_simp(v_arg_587_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref(v___x_605_);
v___x_607_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_572_, v_fn_586_, v_arg_587_, v_a_591_, v_a_606_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_607_;
}
else
{
lean_dec(v_a_591_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
return v___x_605_;
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_608_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_608_, 1, v___x_585_);
v___x_609_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_572_, v_fn_586_, v_arg_587_, v_a_591_, v___x_608_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_609_;
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_591_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
v_a_610_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_602_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_602_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_597_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
v___x_628_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
v___x_629_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_628_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_629_;
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_591_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
v_a_631_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_594_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_594_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_a_591_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
v_a_639_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_592_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_592_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_e_572_);
lean_dec_ref(v_fn_586_);
return v___x_590_;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v_e_572_);
lean_dec_ref(v_simpFn_571_);
v___x_647_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
v___x_648_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_647_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_648_;
}
}
else
{
lean_object* v___x_649_; 
lean_inc(v_a_582_);
lean_inc_ref(v_a_581_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
v___x_649_ = lean_apply_11(v_simpFn_571_, v_e_572_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, lean_box(0));
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* v_simpFn_650_, lean_object* v_e_651_, lean_object* v_i_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_650_, v_e_651_, v_i_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec(v_i_652_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* v_e_664_, lean_object* v_numArgs_665_, lean_object* v_simpFn_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_666_, v_e_664_, v_numArgs_665_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* v_e_678_, lean_object* v_numArgs_679_, lean_object* v_simpFn_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_678_, v_numArgs_679_, v_simpFn_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec(v_numArgs_679_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_694_ = lean_unsigned_to_nat(13u);
v___x_695_ = lean_unsigned_to_nat(172u);
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_698_ = l_mkPanicMessageWithDecl(v___x_697_, v___x_696_, v___x_695_, v___x_694_, v___x_693_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* v_simpFn_699_, lean_object* v_e_700_, lean_object* v_i_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_nat_dec_eq(v_i_701_, v___x_712_);
if (v___x_713_ == 0)
{
if (lean_obj_tag(v_e_700_) == 5)
{
lean_object* v_fn_714_; lean_object* v_arg_715_; lean_object* v___x_716_; lean_object* v_i_717_; lean_object* v___x_718_; 
v_fn_714_ = lean_ctor_get(v_e_700_, 0);
lean_inc_ref_n(v_fn_714_, 2);
v_arg_715_ = lean_ctor_get(v_e_700_, 1);
lean_inc_ref(v_arg_715_);
v___x_716_ = lean_unsigned_to_nat(1u);
v_i_717_ = lean_nat_sub(v_i_701_, v___x_716_);
v___x_718_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_699_, v_fn_714_, v_i_717_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_i_717_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
if (lean_obj_tag(v_a_719_) == 0)
{
lean_dec_ref(v_a_719_);
lean_dec_ref(v_arg_715_);
lean_dec_ref(v_e_700_);
lean_dec_ref(v_fn_714_);
return v___x_718_;
}
else
{
lean_object* v_e_x27_720_; lean_object* v_proof_721_; uint8_t v_done_722_; uint8_t v_contextDependent_723_; lean_object* v___x_724_; 
lean_dec_ref(v___x_718_);
v_e_x27_720_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_e_x27_720_);
v_proof_721_ = lean_ctor_get(v_a_719_, 1);
lean_inc_ref(v_proof_721_);
v_done_722_ = lean_ctor_get_uint8(v_a_719_, sizeof(void*)*2);
v_contextDependent_723_ = lean_ctor_get_uint8(v_a_719_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_719_);
v___x_724_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_700_, v_fn_714_, v_arg_715_, v_e_x27_720_, v_proof_721_, v_done_722_, v_contextDependent_723_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_724_;
}
}
else
{
lean_dec_ref(v_arg_715_);
lean_dec_ref(v_e_700_);
lean_dec_ref(v_fn_714_);
return v___x_718_;
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_e_700_);
lean_dec_ref(v_simpFn_699_);
v___x_725_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
v___x_726_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_725_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; 
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_a_705_);
lean_inc(v_a_704_);
lean_inc_ref(v_a_703_);
lean_inc(v_a_702_);
v___x_727_ = lean_apply_11(v_simpFn_699_, v_e_700_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, lean_box(0));
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* v_simpFn_728_, lean_object* v_e_729_, lean_object* v_i_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_728_, v_e_729_, v_i_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec(v_i_730_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* v_e_742_, lean_object* v_numArgs_743_, lean_object* v_simpFn_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_744_, v_e_742_, v_numArgs_743_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* v_e_756_, lean_object* v_numArgs_757_, lean_object* v_simpFn_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_756_, v_numArgs_757_, v_simpFn_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec(v_numArgs_757_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(lean_object* v_type_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = l_Lean_Expr_isForall(v_type_773_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_whnfD(v_type_773_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; uint8_t v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
v___x_783_ = l_Lean_Expr_isForall(v_a_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v___x_784_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1);
v___x_785_ = l_Lean_MessageData_ofExpr(v_a_782_);
v___x_786_ = l_Lean_indentD(v___x_785_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_784_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_787_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_782_, v_a_774_);
return v___x_797_;
}
}
else
{
return v___x_781_;
}
}
else
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_type_773_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___boxed(lean_object* v_type_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_type_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_type_807_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_824_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_986__overap_835_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_986__overap_835_ = lean_panic_fn_borrowed(v___x_834_, v_msg_826_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
v___x_836_ = lean_apply_7(v___x_986__overap_835_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_848_ = lean_unsigned_to_nat(47u);
v___x_849_ = lean_unsigned_to_nat(203u);
v___x_850_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_852_ = l_mkPanicMessageWithDecl(v___x_851_, v___x_850_, v___x_849_, v___x_848_, v___x_847_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_853_, lean_object* v_n_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_zero_862_; uint8_t v_isZero_863_; 
v_zero_862_ = lean_unsigned_to_nat(0u);
v_isZero_863_ = lean_nat_dec_eq(v_n_854_, v_zero_862_);
if (v_isZero_863_ == 1)
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Sym_inferType___redArg(v_e_853_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_864_;
}
else
{
lean_object* v_one_865_; lean_object* v_n_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_one_865_ = lean_unsigned_to_nat(1u);
v_n_866_ = lean_nat_sub(v_n_854_, v_one_865_);
v___x_867_ = l_Lean_Expr_appFn_x21(v_e_853_);
lean_dec_ref(v_e_853_);
v___x_868_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_867_, v_n_866_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_n_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref(v___x_868_);
v___x_870_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_a_869_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_881_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_881_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_881_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_881_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 7)
{
lean_object* v_body_875_; lean_object* v___x_877_; 
v_body_875_ = lean_ctor_get(v_a_871_, 2);
lean_inc_ref(v_body_875_);
lean_dec_ref(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_body_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_body_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_del_object(v___x_873_);
lean_dec(v_a_871_);
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_880_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_879_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_880_;
}
}
}
else
{
return v___x_870_;
}
}
else
{
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_882_, lean_object* v_n_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_882_, v_n_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_n_883_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_892_, lean_object* v_a_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___y_902_; lean_object* v___x_905_; uint8_t v_debug_906_; 
v___x_905_ = lean_st_ref_get(v___y_895_);
v_debug_906_ = lean_ctor_get_uint8(v___x_905_, sizeof(void*)*10);
lean_dec(v___x_905_);
if (v_debug_906_ == 0)
{
v___y_902_ = v___y_895_;
goto v___jp_901_;
}
else
{
lean_object* v___x_907_; 
lean_inc_ref(v_f_892_);
v___x_907_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_892_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; 
lean_dec_ref(v___x_907_);
lean_inc_ref(v_a_893_);
v___x_908_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_dec_ref(v___x_908_);
v___y_902_ = v___y_895_;
goto v___jp_901_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_a_893_);
lean_dec_ref(v_f_892_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_a_893_);
lean_dec_ref(v_f_892_);
v_a_917_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_907_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_907_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
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
v___jp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = l_Lean_Expr_app___override(v_f_892_, v_a_893_);
v___x_904_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_903_, v___y_902_);
return v___x_904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_925_, lean_object* v_a_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_925_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_935_, lean_object* v_a_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_935_, v_a_936_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_948_, lean_object* v_a_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_948_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
return v_res_960_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_31792__overap_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
v___x_31792__overap_974_ = lean_panic_fn_borrowed(v___x_973_, v_msg_962_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
v___x_975_ = lean_apply_10(v___x_31792__overap_974_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, lean_box(0));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
return v_res_987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
v___x_992_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_993_ = l_Lean_Expr_const___override(v___x_992_, v___x_991_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_996_ = lean_unsigned_to_nat(52u);
v___x_997_ = lean_unsigned_to_nat(265u);
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1000_ = l_mkPanicMessageWithDecl(v___x_999_, v___x_998_, v___x_997_, v___x_996_, v___x_995_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1002_ = lean_unsigned_to_nat(52u);
v___x_1003_ = lean_unsigned_to_nat(257u);
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1006_ = l_mkPanicMessageWithDecl(v___x_1005_, v___x_1004_, v___x_1003_, v___x_1002_, v___x_1001_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1008_ = lean_unsigned_to_nat(52u);
v___x_1009_ = lean_unsigned_to_nat(272u);
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1012_ = l_mkPanicMessageWithDecl(v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1014_ = lean_unsigned_to_nat(26u);
v___x_1015_ = lean_unsigned_to_nat(250u);
v___x_1016_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1017_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1018_ = l_mkPanicMessageWithDecl(v___x_1017_, v___x_1016_, v___x_1015_, v___x_1014_, v___x_1013_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1022_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1024_, lean_object* v_e_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_nat_dec_eq(v_i_1024_, v___x_1036_);
if (v___x_1037_ == 0)
{
if (lean_obj_tag(v_e_1025_) == 5)
{
lean_object* v_fn_1038_; lean_object* v_arg_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_fn_1038_ = lean_ctor_get(v_e_1025_, 0);
lean_inc_ref_n(v_fn_1038_, 2);
v_arg_1039_ = lean_ctor_get(v_e_1025_, 1);
lean_inc_ref(v_arg_1039_);
lean_dec_ref(v_e_1025_);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_sub(v_i_1024_, v___x_1040_);
v___x_1042_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1041_, v_fn_1038_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1301_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1042_);
v_fst_1044_ = lean_ctor_get(v_a_1043_, 0);
v_snd_1045_ = lean_ctor_get(v_a_1043_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1047_ = v_a_1043_;
v_isShared_1048_ = v_isSharedCheck_1301_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_a_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1301_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; 
lean_inc(v_a_1034_);
lean_inc_ref(v_a_1033_);
lean_inc(v_a_1032_);
lean_inc_ref(v_a_1031_);
lean_inc(v_a_1030_);
lean_inc_ref(v_a_1029_);
lean_inc(v_a_1028_);
lean_inc_ref(v_a_1027_);
lean_inc(v_a_1026_);
lean_inc_ref(v_arg_1039_);
v___x_1049_ = lean_sym_simp(v_arg_1039_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1292_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1292_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1292_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
uint8_t v___y_1055_; uint8_t v___x_1064_; 
v___x_1064_ = 1;
if (lean_obj_tag(v_fst_1044_) == 0)
{
lean_dec(v_snd_1045_);
if (lean_obj_tag(v_a_1050_) == 0)
{
uint8_t v_contextDependent_1065_; 
lean_dec(v___x_1041_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_contextDependent_1065_ = lean_ctor_get_uint8(v_fst_1044_, 1);
lean_dec_ref(v_fst_1044_);
if (v_contextDependent_1065_ == 0)
{
uint8_t v_contextDependent_1066_; 
v_contextDependent_1066_ = lean_ctor_get_uint8(v_a_1050_, 1);
lean_dec_ref(v_a_1050_);
v___y_1055_ = v_contextDependent_1066_;
goto v___jp_1054_;
}
else
{
lean_dec_ref(v_a_1050_);
v___y_1055_ = v___x_1064_;
goto v___jp_1054_;
}
}
else
{
uint8_t v_contextDependent_1067_; lean_object* v_e_x27_1068_; lean_object* v_proof_1069_; uint8_t v_contextDependent_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1052_);
lean_del_object(v___x_1047_);
v_contextDependent_1067_ = lean_ctor_get_uint8(v_fst_1044_, 1);
lean_dec_ref(v_fst_1044_);
v_e_x27_1068_ = lean_ctor_get(v_a_1050_, 0);
v_proof_1069_ = lean_ctor_get(v_a_1050_, 1);
v_contextDependent_1070_ = lean_ctor_get_uint8(v_a_1050_, sizeof(void*)*2 + 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1050_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1072_ = v_a_1050_;
v_isShared_1073_ = v_isSharedCheck_1147_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_proof_1069_);
lean_inc(v_e_x27_1068_);
lean_dec(v_a_1050_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1147_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; 
lean_inc_ref(v_fn_1038_);
v___x_1074_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1038_, v___x_1041_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v___x_1041_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_a_1075_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
if (lean_obj_tag(v_a_1077_) == 7)
{
lean_object* v_binderType_1078_; lean_object* v_body_1079_; lean_object* v___x_1080_; 
v_binderType_1078_ = lean_ctor_get(v_a_1077_, 1);
lean_inc_ref(v_binderType_1078_);
v_body_1079_ = lean_ctor_get(v_a_1077_, 2);
lean_inc_ref(v_body_1079_);
lean_dec_ref(v_a_1077_);
lean_inc_ref(v_e_x27_1068_);
lean_inc_ref(v_fn_1038_);
v___x_1080_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1038_, v_e_x27_1068_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
lean_inc_ref(v_binderType_1078_);
v___x_1082_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1078_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
lean_inc_ref(v_body_1079_);
v___x_1084_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1079_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1104_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1104_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1104_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___y_1096_; 
v___x_1089_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_a_1085_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1083_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_mkConst(v___x_1089_, v___x_1092_);
lean_inc_ref(v_body_1079_);
v___x_1094_ = l_Lean_mkApp6(v___x_1093_, v_binderType_1078_, v_body_1079_, v_arg_1039_, v_e_x27_1068_, v_fn_1038_, v_proof_1069_);
if (v_contextDependent_1067_ == 0)
{
v___y_1096_ = v_contextDependent_1070_;
goto v___jp_1095_;
}
else
{
v___y_1096_ = v___x_1064_;
goto v___jp_1095_;
}
v___jp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___x_1094_);
lean_ctor_set(v___x_1072_, 0, v_a_1081_);
v___x_1098_ = v___x_1072_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v___x_1094_);
v___x_1098_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2, v___x_1037_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2 + 1, v___y_1096_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_body_1079_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1099_);
v___x_1101_ = v___x_1087_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_a_1083_);
lean_dec(v_a_1081_);
lean_dec_ref(v_body_1079_);
lean_dec_ref(v_binderType_1078_);
lean_del_object(v___x_1072_);
lean_dec_ref(v_proof_1069_);
lean_dec_ref(v_e_x27_1068_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1105_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1084_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1084_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1081_);
lean_dec_ref(v_body_1079_);
lean_dec_ref(v_binderType_1078_);
lean_del_object(v___x_1072_);
lean_dec_ref(v_proof_1069_);
lean_dec_ref(v_e_x27_1068_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1113_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1082_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1082_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_body_1079_);
lean_dec_ref(v_binderType_1078_);
lean_del_object(v___x_1072_);
lean_dec_ref(v_proof_1069_);
lean_dec_ref(v_e_x27_1068_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1121_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1080_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1080_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v_a_1077_);
lean_del_object(v___x_1072_);
lean_dec_ref(v_proof_1069_);
lean_dec_ref(v_e_x27_1068_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v___x_1129_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1130_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1129_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
return v___x_1130_;
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_proof_1069_);
lean_dec_ref(v_e_x27_1068_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1131_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1076_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1076_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_proof_1069_);
lean_dec_ref(v_e_x27_1068_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1139_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1074_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1074_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1052_);
lean_del_object(v___x_1047_);
lean_dec(v___x_1041_);
if (lean_obj_tag(v_a_1050_) == 0)
{
lean_object* v_e_x27_1148_; lean_object* v_proof_1149_; uint8_t v_contextDependent_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1218_; 
v_e_x27_1148_ = lean_ctor_get(v_fst_1044_, 0);
v_proof_1149_ = lean_ctor_get(v_fst_1044_, 1);
v_contextDependent_1150_ = lean_ctor_get_uint8(v_fst_1044_, sizeof(void*)*2 + 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_fst_1044_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1152_ = v_fst_1044_;
v_isShared_1153_ = v_isSharedCheck_1218_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_proof_1149_);
lean_inc(v_e_x27_1148_);
lean_dec(v_fst_1044_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1218_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v_contextDependent_1154_; lean_object* v___x_1155_; 
v_contextDependent_1154_ = lean_ctor_get_uint8(v_a_1050_, 1);
lean_dec_ref(v_a_1050_);
v___x_1155_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_snd_1045_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1155_);
if (lean_obj_tag(v_a_1156_) == 7)
{
lean_object* v_binderType_1157_; lean_object* v_body_1158_; lean_object* v___x_1159_; 
v_binderType_1157_ = lean_ctor_get(v_a_1156_, 1);
lean_inc_ref(v_binderType_1157_);
v_body_1158_ = lean_ctor_get(v_a_1156_, 2);
lean_inc_ref(v_body_1158_);
lean_dec_ref(v_a_1156_);
lean_inc_ref(v_arg_1039_);
lean_inc_ref(v_e_x27_1148_);
v___x_1159_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1148_, v_arg_1039_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v___x_1159_);
lean_inc_ref(v_binderType_1157_);
v___x_1161_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1157_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
lean_inc_ref(v_body_1158_);
v___x_1163_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1158_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1183_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1183_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1183_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___y_1175_; 
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1164_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1162_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_mkConst(v___x_1168_, v___x_1171_);
lean_inc_ref(v_body_1158_);
v___x_1173_ = l_Lean_mkApp6(v___x_1172_, v_binderType_1157_, v_body_1158_, v_fn_1038_, v_e_x27_1148_, v_proof_1149_, v_arg_1039_);
if (v_contextDependent_1150_ == 0)
{
v___y_1175_ = v_contextDependent_1154_;
goto v___jp_1174_;
}
else
{
v___y_1175_ = v___x_1064_;
goto v___jp_1174_;
}
v___jp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1173_);
lean_ctor_set(v___x_1152_, 0, v_a_1160_);
v___x_1177_ = v___x_1152_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1160_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1173_);
v___x_1177_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*2, v___x_1037_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*2 + 1, v___y_1175_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_body_1158_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1178_);
v___x_1180_ = v___x_1166_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1162_);
lean_dec(v_a_1160_);
lean_dec_ref(v_body_1158_);
lean_dec_ref(v_binderType_1157_);
lean_del_object(v___x_1152_);
lean_dec_ref(v_proof_1149_);
lean_dec_ref(v_e_x27_1148_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1184_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1163_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1163_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_a_1160_);
lean_dec_ref(v_body_1158_);
lean_dec_ref(v_binderType_1157_);
lean_del_object(v___x_1152_);
lean_dec_ref(v_proof_1149_);
lean_dec_ref(v_e_x27_1148_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1192_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1161_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1161_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_body_1158_);
lean_dec_ref(v_binderType_1157_);
lean_del_object(v___x_1152_);
lean_dec_ref(v_proof_1149_);
lean_dec_ref(v_e_x27_1148_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1200_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1159_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1159_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_a_1156_);
lean_del_object(v___x_1152_);
lean_dec_ref(v_proof_1149_);
lean_dec_ref(v_e_x27_1148_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v___x_1208_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1209_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1208_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
return v___x_1209_;
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1152_);
lean_dec_ref(v_proof_1149_);
lean_dec_ref(v_e_x27_1148_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1210_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1155_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1155_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1219_; lean_object* v_proof_1220_; uint8_t v_contextDependent_1221_; lean_object* v_e_x27_1222_; lean_object* v_proof_1223_; uint8_t v_contextDependent_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1291_; 
v_e_x27_1219_ = lean_ctor_get(v_fst_1044_, 0);
lean_inc_ref(v_e_x27_1219_);
v_proof_1220_ = lean_ctor_get(v_fst_1044_, 1);
lean_inc_ref(v_proof_1220_);
v_contextDependent_1221_ = lean_ctor_get_uint8(v_fst_1044_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_1044_);
v_e_x27_1222_ = lean_ctor_get(v_a_1050_, 0);
v_proof_1223_ = lean_ctor_get(v_a_1050_, 1);
v_contextDependent_1224_ = lean_ctor_get_uint8(v_a_1050_, sizeof(void*)*2 + 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_a_1050_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1226_ = v_a_1050_;
v_isShared_1227_ = v_isSharedCheck_1291_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_proof_1223_);
lean_inc(v_e_x27_1222_);
lean_dec(v_a_1050_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1291_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; 
v___x_1228_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_snd_1045_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref(v___x_1228_);
if (lean_obj_tag(v_a_1229_) == 7)
{
lean_object* v_binderType_1230_; lean_object* v_body_1231_; lean_object* v___x_1232_; 
v_binderType_1230_ = lean_ctor_get(v_a_1229_, 1);
lean_inc_ref(v_binderType_1230_);
v_body_1231_ = lean_ctor_get(v_a_1229_, 2);
lean_inc_ref(v_body_1231_);
lean_dec_ref(v_a_1229_);
lean_inc_ref(v_e_x27_1222_);
lean_inc_ref(v_e_x27_1219_);
v___x_1232_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1219_, v_e_x27_1222_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
lean_inc_ref(v_binderType_1230_);
v___x_1234_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1230_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
lean_inc_ref(v_body_1231_);
v___x_1236_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1231_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1256_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1256_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1256_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___y_1248_; 
v___x_1241_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_a_1237_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_a_1235_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_mkConst(v___x_1241_, v___x_1244_);
lean_inc_ref(v_body_1231_);
v___x_1246_ = l_Lean_mkApp8(v___x_1245_, v_binderType_1230_, v_body_1231_, v_fn_1038_, v_e_x27_1219_, v_arg_1039_, v_e_x27_1222_, v_proof_1220_, v_proof_1223_);
if (v_contextDependent_1221_ == 0)
{
v___y_1248_ = v_contextDependent_1224_;
goto v___jp_1247_;
}
else
{
v___y_1248_ = v___x_1064_;
goto v___jp_1247_;
}
v___jp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1246_);
lean_ctor_set(v___x_1226_, 0, v_a_1233_);
v___x_1250_ = v___x_1226_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1233_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1246_);
v___x_1250_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_ctor_set_uint8(v___x_1250_, sizeof(void*)*2, v___x_1037_);
lean_ctor_set_uint8(v___x_1250_, sizeof(void*)*2 + 1, v___y_1248_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_body_1231_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1251_);
v___x_1253_ = v___x_1239_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
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
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1235_);
lean_dec(v_a_1233_);
lean_dec_ref(v_body_1231_);
lean_dec_ref(v_binderType_1230_);
lean_del_object(v___x_1226_);
lean_dec_ref(v_proof_1223_);
lean_dec_ref(v_e_x27_1222_);
lean_dec_ref(v_proof_1220_);
lean_dec_ref(v_e_x27_1219_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1257_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1236_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1236_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1233_);
lean_dec_ref(v_body_1231_);
lean_dec_ref(v_binderType_1230_);
lean_del_object(v___x_1226_);
lean_dec_ref(v_proof_1223_);
lean_dec_ref(v_e_x27_1222_);
lean_dec_ref(v_proof_1220_);
lean_dec_ref(v_e_x27_1219_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1265_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1234_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1234_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_body_1231_);
lean_dec_ref(v_binderType_1230_);
lean_del_object(v___x_1226_);
lean_dec_ref(v_proof_1223_);
lean_dec_ref(v_e_x27_1222_);
lean_dec_ref(v_proof_1220_);
lean_dec_ref(v_e_x27_1219_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1273_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1232_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1232_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v_a_1229_);
lean_del_object(v___x_1226_);
lean_dec_ref(v_proof_1223_);
lean_dec_ref(v_e_x27_1222_);
lean_dec_ref(v_proof_1220_);
lean_dec_ref(v_e_x27_1219_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v___x_1281_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1282_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1281_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
return v___x_1282_;
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1226_);
lean_dec_ref(v_proof_1223_);
lean_dec_ref(v_e_x27_1222_);
lean_dec_ref(v_proof_1220_);
lean_dec_ref(v_e_x27_1219_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1283_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1228_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1228_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1055_);
v___x_1057_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1057_);
lean_ctor_set(v___x_1047_, 0, v___x_1056_);
v___x_1059_ = v___x_1047_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1059_);
v___x_1061_ = v___x_1052_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_del_object(v___x_1047_);
lean_dec(v_snd_1045_);
lean_dec(v_fst_1044_);
lean_dec(v___x_1041_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
v_a_1293_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1049_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1049_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
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
lean_dec(v___x_1041_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_fn_1038_);
return v___x_1042_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v_e_1025_);
v___x_1302_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1303_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1302_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
return v___x_1303_;
}
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_e_1025_);
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1306_, lean_object* v_e_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1306_, v_e_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec(v_i_1306_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1319_, lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1319_, v_e_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1340_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_fst_1336_; lean_object* v___x_1338_; 
v_fst_1336_ = lean_ctor_get(v_a_1332_, 0);
lean_inc(v_fst_1336_);
lean_dec(v_a_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_fst_1336_);
v___x_1338_ = v___x_1334_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_fst_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1341_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1331_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1331_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1349_, lean_object* v_e_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1349_, v_e_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_n_1349_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1362_, lean_object* v_prefixSize_1363_, lean_object* v_suffixSize_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_numArgs_1375_; uint8_t v___x_1376_; 
v_numArgs_1375_ = l_Lean_Expr_getAppNumArgs(v_e_1362_);
v___x_1376_ = lean_nat_dec_le(v_numArgs_1375_, v_prefixSize_1363_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_nat_add(v_prefixSize_1363_, v_suffixSize_1364_);
v___x_1378_ = lean_nat_dec_lt(v___x_1377_, v_numArgs_1375_);
lean_dec(v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_suffixSize_1364_);
v___x_1379_ = lean_nat_sub(v_numArgs_1375_, v_prefixSize_1363_);
lean_dec(v_numArgs_1375_);
v___x_1380_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1379_, v_e_1362_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
lean_dec(v___x_1379_);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1381_ = lean_nat_sub(v_numArgs_1375_, v_prefixSize_1363_);
lean_dec(v_numArgs_1375_);
v___x_1382_ = lean_nat_sub(v___x_1381_, v_suffixSize_1364_);
lean_dec(v___x_1381_);
v___x_1383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1383_, 0, v_suffixSize_1364_);
v___x_1384_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1383_, v_e_1362_, v___x_1382_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
lean_dec(v___x_1382_);
return v___x_1384_;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v_numArgs_1375_);
lean_dec(v_suffixSize_1364_);
lean_dec_ref(v_e_1362_);
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1387_, lean_object* v_prefixSize_1388_, lean_object* v_suffixSize_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1387_, v_prefixSize_1388_, v_suffixSize_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec(v_prefixSize_1388_);
return v_res_1400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1402_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1403_ = lean_unsigned_to_nat(13u);
v___x_1404_ = lean_unsigned_to_nat(308u);
v___x_1405_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1407_ = l_mkPanicMessageWithDecl(v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_, v___x_1402_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1408_, lean_object* v_i_1409_, lean_object* v_e_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_nat_dec_eq(v_i_1409_, v___x_1421_);
if (v___x_1422_ == 0)
{
if (lean_obj_tag(v_e_1410_) == 5)
{
lean_object* v_fn_1423_; lean_object* v_arg_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_fn_1423_ = lean_ctor_get(v_e_1410_, 0);
lean_inc_ref_n(v_fn_1423_, 2);
v_arg_1424_ = lean_ctor_get(v_e_1410_, 1);
lean_inc_ref(v_arg_1424_);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_sub(v_i_1409_, v___x_1425_);
v___x_1427_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1408_, v___x_1426_, v_fn_1423_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1447_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1447_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1447_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = lean_array_fget_borrowed(v_rewritable_1408_, v___x_1426_);
lean_dec(v___x_1426_);
v___x_1433_ = lean_unbox(v___x_1432_);
if (v___x_1433_ == 0)
{
if (lean_obj_tag(v_a_1428_) == 0)
{
uint8_t v_contextDependent_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_e_1410_);
lean_dec_ref(v_fn_1423_);
v_contextDependent_1434_ = lean_ctor_get_uint8(v_a_1428_, 1);
lean_dec_ref(v_a_1428_);
v___x_1435_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1434_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1435_);
v___x_1437_ = v___x_1430_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
lean_object* v_e_x27_1439_; lean_object* v_proof_1440_; uint8_t v_contextDependent_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
lean_del_object(v___x_1430_);
v_e_x27_1439_ = lean_ctor_get(v_a_1428_, 0);
lean_inc_ref(v_e_x27_1439_);
v_proof_1440_ = lean_ctor_get(v_a_1428_, 1);
lean_inc_ref(v_proof_1440_);
v_contextDependent_1441_ = lean_ctor_get_uint8(v_a_1428_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1428_);
v___x_1442_ = lean_unbox(v___x_1432_);
v___x_1443_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1410_, v_fn_1423_, v_arg_1424_, v_e_x27_1439_, v_proof_1440_, v___x_1442_, v_contextDependent_1441_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1443_;
}
}
else
{
lean_object* v___x_1444_; 
lean_del_object(v___x_1430_);
lean_inc(v_a_1419_);
lean_inc_ref(v_a_1418_);
lean_inc(v_a_1417_);
lean_inc_ref(v_a_1416_);
lean_inc(v_a_1415_);
lean_inc_ref(v_a_1414_);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
lean_inc(v_a_1411_);
lean_inc_ref(v_arg_1424_);
v___x_1444_ = lean_sym_simp(v_arg_1424_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1410_, v_fn_1423_, v_arg_1424_, v_a_1428_, v_a_1445_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1446_;
}
else
{
lean_dec(v_a_1428_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_e_1410_);
lean_dec_ref(v_fn_1423_);
return v___x_1444_;
}
}
}
}
else
{
lean_dec(v___x_1426_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_e_1410_);
lean_dec_ref(v_fn_1423_);
return v___x_1427_;
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_e_1410_);
v___x_1448_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1449_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1448_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1449_;
}
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v_e_1410_);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1452_, lean_object* v_i_1453_, lean_object* v_e_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1452_, v_i_1453_, v_e_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec(v_i_1453_);
lean_dec_ref(v_rewritable_1452_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1466_, lean_object* v_i_1467_, lean_object* v_e_1468_, lean_object* v_h_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1466_, v_i_1467_, v_e_1468_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1481_, lean_object* v_i_1482_, lean_object* v_e_1483_, lean_object* v_h_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1481_, v_i_1482_, v_e_1483_, v_h_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec(v_i_1482_);
lean_dec_ref(v_rewritable_1481_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1496_, lean_object* v___x_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1496_, v___x_1497_, v_x_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1510_, lean_object* v___x_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1510_, v___x_1511_, v_x_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec(v___x_1511_);
lean_dec_ref(v_rewritable_1510_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1524_, lean_object* v_rewritable_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_numArgs_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_numArgs_1536_ = l_Lean_Expr_getAppNumArgs(v_e_1524_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_nat_dec_eq(v_numArgs_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = lean_array_get_size(v_rewritable_1525_);
v___x_1540_ = lean_nat_dec_lt(v___x_1539_, v_numArgs_1536_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1525_, v_numArgs_1536_, v_e_1524_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_numArgs_1536_);
lean_dec_ref(v_rewritable_1525_);
return v___x_1541_;
}
else
{
lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___f_1542_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1542_, 0, v_rewritable_1525_);
lean_closure_set(v___f_1542_, 1, v___x_1539_);
v___x_1543_ = lean_nat_sub(v_numArgs_1536_, v___x_1539_);
lean_dec(v_numArgs_1536_);
v___x_1544_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1542_, v_e_1524_, v___x_1543_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v___x_1543_);
return v___x_1544_;
}
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec(v_numArgs_1536_);
lean_dec_ref(v_rewritable_1525_);
lean_dec_ref(v_e_1524_);
v___x_1545_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1547_, lean_object* v_rewritable_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1547_, v_rewritable_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1560_, lean_object* v_numEqs_1561_, lean_object* v_result_1562_){
_start:
{
if (lean_obj_tag(v_result_1562_) == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_dec(v_numEqs_1561_);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_array_get_size(v_argResults_1560_);
v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_dec_ref(v_result_1562_);
return v_argResults_1560_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_array_push(v_argResults_1560_, v_result_1562_);
return v___x_1566_;
}
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_array_get_size(v_argResults_1560_);
v___x_1568_ = lean_nat_dec_lt(v___x_1567_, v_numEqs_1561_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec(v_numEqs_1561_);
v___x_1569_ = lean_array_push(v_argResults_1560_, v_result_1562_);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_argResults_1560_);
v___x_1570_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1571_ = lean_mk_array(v_numEqs_1561_, v___x_1570_);
v___x_1572_ = lean_array_push(v___x_1571_, v_result_1562_);
return v___x_1572_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1574_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1575_ = lean_unsigned_to_nat(13u);
v___x_1576_ = lean_unsigned_to_nat(429u);
v___x_1577_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1578_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1579_ = l_mkPanicMessageWithDecl(v___x_1578_, v___x_1577_, v___x_1576_, v___x_1575_, v___x_1574_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1580_, lean_object* v_mkNonRflResult_1581_, lean_object* v_e_1582_, lean_object* v_i_1583_, lean_object* v_numEqs_1584_, lean_object* v_argResults_1585_, uint8_t v_anyCD_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
if (lean_obj_tag(v_e_1582_) == 5)
{
lean_object* v_fn_1597_; lean_object* v_arg_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_fn_1597_ = lean_ctor_get(v_e_1582_, 0);
lean_inc_ref(v_fn_1597_);
v_arg_1598_ = lean_ctor_get(v_e_1582_, 1);
lean_inc_ref(v_arg_1598_);
lean_dec_ref(v_e_1582_);
v___x_1612_ = 0;
v___x_1613_ = lean_box(v___x_1612_);
v___x_1614_ = lean_array_get(v___x_1613_, v_argKinds_1580_, v_i_1583_);
lean_dec(v___x_1613_);
v___x_1615_ = lean_unbox(v___x_1614_);
lean_dec(v___x_1614_);
switch(v___x_1615_)
{
case 5:
{
lean_dec_ref(v_arg_1598_);
v___y_1600_ = v_a_1587_;
v___y_1601_ = v_a_1588_;
v___y_1602_ = v_a_1589_;
v___y_1603_ = v_a_1590_;
v___y_1604_ = v_a_1591_;
v___y_1605_ = v_a_1592_;
v___y_1606_ = v_a_1593_;
v___y_1607_ = v_a_1594_;
v___y_1608_ = v_a_1595_;
goto v___jp_1599_;
}
case 0:
{
lean_dec_ref(v_arg_1598_);
v___y_1600_ = v_a_1587_;
v___y_1601_ = v_a_1588_;
v___y_1602_ = v_a_1589_;
v___y_1603_ = v_a_1590_;
v___y_1604_ = v_a_1591_;
v___y_1605_ = v_a_1592_;
v___y_1606_ = v_a_1593_;
v___y_1607_ = v_a_1594_;
v___y_1608_ = v_a_1595_;
goto v___jp_1599_;
}
case 3:
{
lean_dec_ref(v_arg_1598_);
v___y_1600_ = v_a_1587_;
v___y_1601_ = v_a_1588_;
v___y_1602_ = v_a_1589_;
v___y_1603_ = v_a_1590_;
v___y_1604_ = v_a_1591_;
v___y_1605_ = v_a_1592_;
v___y_1606_ = v_a_1593_;
v___y_1607_ = v_a_1594_;
v___y_1608_ = v_a_1595_;
goto v___jp_1599_;
}
case 2:
{
lean_object* v___x_1616_; 
lean_inc(v_a_1595_);
lean_inc_ref(v_a_1594_);
lean_inc(v_a_1593_);
lean_inc_ref(v_a_1592_);
lean_inc(v_a_1591_);
lean_inc_ref(v_a_1590_);
lean_inc(v_a_1589_);
lean_inc_ref(v_a_1588_);
lean_inc(v_a_1587_);
v___x_1616_ = lean_sym_simp(v_arg_1598_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc_n(v_a_1617_, 2);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = lean_nat_sub(v_i_1583_, v___x_1618_);
lean_dec(v_i_1583_);
v___x_1620_ = lean_nat_add(v_numEqs_1584_, v___x_1618_);
v___x_1621_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1585_, v_numEqs_1584_, v_a_1617_);
if (v_anyCD_1586_ == 0)
{
if (lean_obj_tag(v_a_1617_) == 0)
{
uint8_t v_contextDependent_1622_; 
v_contextDependent_1622_ = lean_ctor_get_uint8(v_a_1617_, 1);
lean_dec_ref(v_a_1617_);
v_e_1582_ = v_fn_1597_;
v_i_1583_ = v___x_1619_;
v_numEqs_1584_ = v___x_1620_;
v_argResults_1585_ = v___x_1621_;
v_anyCD_1586_ = v_contextDependent_1622_;
goto _start;
}
else
{
uint8_t v_contextDependent_1624_; 
v_contextDependent_1624_ = lean_ctor_get_uint8(v_a_1617_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1617_);
v_e_1582_ = v_fn_1597_;
v_i_1583_ = v___x_1619_;
v_numEqs_1584_ = v___x_1620_;
v_argResults_1585_ = v___x_1621_;
v_anyCD_1586_ = v_contextDependent_1624_;
goto _start;
}
}
else
{
lean_dec(v_a_1617_);
v_e_1582_ = v_fn_1597_;
v_i_1583_ = v___x_1619_;
v_numEqs_1584_ = v___x_1620_;
v_argResults_1585_ = v___x_1621_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_1597_);
lean_dec_ref(v_argResults_1585_);
lean_dec(v_numEqs_1584_);
lean_dec(v_i_1583_);
lean_dec_ref(v_mkNonRflResult_1581_);
return v___x_1616_;
}
}
default: 
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec_ref(v_arg_1598_);
lean_dec_ref(v_fn_1597_);
lean_dec_ref(v_argResults_1585_);
lean_dec(v_numEqs_1584_);
lean_dec(v_i_1583_);
lean_dec_ref(v_mkNonRflResult_1581_);
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1628_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1627_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1628_;
}
}
v___jp_1599_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_sub(v_i_1583_, v___x_1609_);
lean_dec(v_i_1583_);
v_e_1582_ = v_fn_1597_;
v_i_1583_ = v___x_1610_;
v_a_1587_ = v___y_1600_;
v_a_1588_ = v___y_1601_;
v_a_1589_ = v___y_1602_;
v_a_1590_ = v___y_1603_;
v_a_1591_ = v___y_1604_;
v_a_1592_ = v___y_1605_;
v_a_1593_ = v___y_1606_;
v_a_1594_ = v___y_1607_;
v_a_1595_ = v___y_1608_;
goto _start;
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
lean_dec(v_numEqs_1584_);
lean_dec(v_i_1583_);
lean_dec_ref(v_e_1582_);
v___x_1629_ = lean_array_get_size(v_argResults_1585_);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_nat_dec_eq(v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = l_Array_reverse___redArg(v_argResults_1585_);
lean_inc(v_a_1595_);
lean_inc_ref(v_a_1594_);
lean_inc(v_a_1593_);
lean_inc_ref(v_a_1592_);
lean_inc(v_a_1591_);
lean_inc_ref(v_a_1590_);
lean_inc(v_a_1589_);
lean_inc_ref(v_a_1588_);
lean_inc(v_a_1587_);
v___x_1633_ = lean_apply_11(v_mkNonRflResult_1581_, v___x_1632_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, lean_box(0));
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; uint8_t v___y_1639_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
if (v_anyCD_1586_ == 0)
{
lean_dec(v_a_1634_);
return v___x_1633_;
}
else
{
if (lean_obj_tag(v_a_1634_) == 0)
{
uint8_t v_contextDependent_1640_; 
v_contextDependent_1640_ = lean_ctor_get_uint8(v_a_1634_, 1);
v___y_1639_ = v_contextDependent_1640_;
goto v___jp_1638_;
}
else
{
uint8_t v_contextDependent_1641_; 
v_contextDependent_1641_ = lean_ctor_get_uint8(v_a_1634_, sizeof(void*)*2 + 1);
v___y_1639_ = v_contextDependent_1641_;
goto v___jp_1638_;
}
}
v___jp_1635_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1634_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
v___jp_1638_:
{
if (v___y_1639_ == 0)
{
lean_dec_ref(v___x_1633_);
goto v___jp_1635_;
}
else
{
if (v___x_1631_ == 0)
{
lean_dec(v_a_1634_);
return v___x_1633_;
}
else
{
lean_dec_ref(v___x_1633_);
goto v___jp_1635_;
}
}
}
}
else
{
return v___x_1633_;
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v_argResults_1585_);
lean_dec_ref(v_mkNonRflResult_1581_);
v___x_1642_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_1586_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object** _args){
lean_object* v_argKinds_1644_ = _args[0];
lean_object* v_mkNonRflResult_1645_ = _args[1];
lean_object* v_e_1646_ = _args[2];
lean_object* v_i_1647_ = _args[3];
lean_object* v_numEqs_1648_ = _args[4];
lean_object* v_argResults_1649_ = _args[5];
lean_object* v_anyCD_1650_ = _args[6];
lean_object* v_a_1651_ = _args[7];
lean_object* v_a_1652_ = _args[8];
lean_object* v_a_1653_ = _args[9];
lean_object* v_a_1654_ = _args[10];
lean_object* v_a_1655_ = _args[11];
lean_object* v_a_1656_ = _args[12];
lean_object* v_a_1657_ = _args[13];
lean_object* v_a_1658_ = _args[14];
lean_object* v_a_1659_ = _args[15];
lean_object* v_a_1660_ = _args[16];
_start:
{
uint8_t v_anyCD_boxed_1661_; lean_object* v_res_1662_; 
v_anyCD_boxed_1661_ = lean_unbox(v_anyCD_1650_);
v_res_1662_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1644_, v_mkNonRflResult_1645_, v_e_1646_, v_i_1647_, v_numEqs_1648_, v_argResults_1649_, v_anyCD_boxed_1661_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_argKinds_1644_);
return v_res_1662_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_21488__overap_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
v___x_21488__overap_1676_ = lean_panic_fn_borrowed(v___x_1675_, v_msg_1664_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc_ref(v___y_1668_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
v___x_1677_ = lean_apply_10(v___x_21488__overap_1676_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, lean_box(0));
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* v_msg_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
return v_res_1689_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(uint8_t v___x_1690_, lean_object* v_as_1691_, size_t v_i_1692_, size_t v_stop_1693_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_eq(v_i_1692_, v_stop_1693_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; uint8_t v___y_1697_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1695_ = 1;
v___x_1701_ = lean_array_uget_borrowed(v_as_1691_, v_i_1692_);
v___x_1702_ = lean_unbox(v___x_1701_);
if (v___x_1702_ == 3)
{
v___y_1697_ = v___x_1690_;
goto v___jp_1696_;
}
else
{
v___y_1697_ = v___x_1694_;
goto v___jp_1696_;
}
v___jp_1696_:
{
if (v___y_1697_ == 0)
{
size_t v___x_1698_; size_t v___x_1699_; 
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1692_, v___x_1698_);
v_i_1692_ = v___x_1699_;
goto _start;
}
else
{
return v___x_1695_;
}
}
}
else
{
uint8_t v___x_1703_; 
v___x_1703_ = 0;
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object* v___x_1704_, lean_object* v_as_1705_, lean_object* v_i_1706_, lean_object* v_stop_1707_){
_start:
{
uint8_t v___x_23297__boxed_1708_; size_t v_i_boxed_1709_; size_t v_stop_boxed_1710_; uint8_t v_res_1711_; lean_object* v_r_1712_; 
v___x_23297__boxed_1708_ = lean_unbox(v___x_1704_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_stop_boxed_1710_ = lean_unbox_usize(v_stop_1707_);
lean_dec(v_stop_1707_);
v_res_1711_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_23297__boxed_1708_, v_as_1705_, v_i_boxed_1709_, v_stop_boxed_1710_);
lean_dec_ref(v_as_1705_);
v_r_1712_ = lean_box(v_res_1711_);
return v_r_1712_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object* v_as_1713_, size_t v_i_1714_, size_t v_stop_1715_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_eq(v_i_1714_, v_stop_1715_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; uint8_t v___y_1719_; lean_object* v___x_1723_; 
v___x_1717_ = 1;
v___x_1723_ = lean_array_uget_borrowed(v_as_1713_, v_i_1714_);
if (lean_obj_tag(v___x_1723_) == 0)
{
uint8_t v_contextDependent_1724_; 
v_contextDependent_1724_ = lean_ctor_get_uint8(v___x_1723_, 1);
v___y_1719_ = v_contextDependent_1724_;
goto v___jp_1718_;
}
else
{
uint8_t v_contextDependent_1725_; 
v_contextDependent_1725_ = lean_ctor_get_uint8(v___x_1723_, sizeof(void*)*2 + 1);
v___y_1719_ = v_contextDependent_1725_;
goto v___jp_1718_;
}
v___jp_1718_:
{
if (v___y_1719_ == 0)
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1714_, v___x_1720_);
v_i_1714_ = v___x_1721_;
goto _start;
}
else
{
return v___x_1717_;
}
}
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = 0;
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v_as_1727_, lean_object* v_i_1728_, lean_object* v_stop_1729_){
_start:
{
size_t v_i_boxed_1730_; size_t v_stop_boxed_1731_; uint8_t v_res_1732_; lean_object* v_r_1733_; 
v_i_boxed_1730_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_stop_boxed_1731_ = lean_unbox_usize(v_stop_1729_);
lean_dec(v_stop_1729_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1727_, v_i_boxed_1730_, v_stop_boxed_1731_);
lean_dec_ref(v_as_1727_);
v_r_1733_ = lean_box(v_res_1732_);
return v_r_1733_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1736_ = lean_unsigned_to_nat(13u);
v___x_1737_ = lean_unsigned_to_nat(401u);
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1740_ = l_mkPanicMessageWithDecl(v___x_1739_, v___x_1738_, v___x_1737_, v___x_1736_, v___x_1735_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1741_, lean_object* v_as_1742_, size_t v_sz_1743_, size_t v_i_1744_, lean_object* v_b_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_a_1757_; uint8_t v___x_1761_; 
v___x_1761_ = lean_usize_dec_lt(v_i_1744_, v_sz_1743_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_b_1745_);
return v___x_1762_;
}
else
{
lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1958_; 
v_snd_1763_ = lean_ctor_get(v_b_1745_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_b_1745_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v_b_1745_, 0);
lean_dec(v_unused_1959_);
v___x_1765_ = v_b_1745_;
v_isShared_1766_ = v_isSharedCheck_1958_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_dec(v_b_1745_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1958_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_snd_1767_; lean_object* v_snd_1768_; lean_object* v_snd_1769_; lean_object* v_snd_1770_; lean_object* v_fst_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1956_; 
v_snd_1767_ = lean_ctor_get(v_snd_1763_, 1);
lean_inc(v_snd_1767_);
v_snd_1768_ = lean_ctor_get(v_snd_1767_, 1);
lean_inc(v_snd_1768_);
v_snd_1769_ = lean_ctor_get(v_snd_1768_, 1);
lean_inc(v_snd_1769_);
v_snd_1770_ = lean_ctor_get(v_snd_1769_, 1);
lean_inc(v_snd_1770_);
v_fst_1771_ = lean_ctor_get(v_snd_1763_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_snd_1763_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v_snd_1763_, 1);
lean_dec(v_unused_1957_);
v___x_1773_ = v_snd_1763_;
v_isShared_1774_ = v_isSharedCheck_1956_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_fst_1771_);
lean_dec(v_snd_1763_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1956_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_fst_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1954_; 
v_fst_1775_ = lean_ctor_get(v_snd_1767_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_snd_1767_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v_snd_1767_, 1);
lean_dec(v_unused_1955_);
v___x_1777_ = v_snd_1767_;
v_isShared_1778_ = v_isSharedCheck_1954_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_fst_1775_);
lean_dec(v_snd_1767_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1954_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_fst_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1952_; 
v_fst_1779_ = lean_ctor_get(v_snd_1768_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_snd_1768_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; 
v_unused_1953_ = lean_ctor_get(v_snd_1768_, 1);
lean_dec(v_unused_1953_);
v___x_1781_ = v_snd_1768_;
v_isShared_1782_ = v_isSharedCheck_1952_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_fst_1779_);
lean_dec(v_snd_1768_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1952_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_fst_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1950_; 
v_fst_1783_ = lean_ctor_get(v_snd_1769_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_snd_1769_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v_snd_1769_, 1);
lean_dec(v_unused_1951_);
v___x_1785_ = v_snd_1769_;
v_isShared_1786_ = v_isSharedCheck_1950_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_fst_1783_);
lean_dec(v_snd_1769_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1950_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_array_1787_; lean_object* v_start_1788_; lean_object* v_stop_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_array_1787_ = lean_ctor_get(v_snd_1770_, 0);
v_start_1788_ = lean_ctor_get(v_snd_1770_, 1);
v_stop_1789_ = lean_ctor_get(v_snd_1770_, 2);
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_nat_dec_lt(v_start_1788_, v_stop_1789_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1793_; 
if (v_isShared_1786_ == 0)
{
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_fst_1783_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_snd_1770_);
v___x_1793_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 1, v___x_1793_);
v___x_1795_ = v___x_1781_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v___x_1795_);
v___x_1797_ = v___x_1777_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_fst_1775_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1797_);
v___x_1799_ = v___x_1773_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_fst_1771_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1801_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1799_);
lean_ctor_set(v___x_1765_, 0, v___x_1790_);
v___x_1801_ = v___x_1765_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
}
}
}
}
else
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1946_; 
lean_inc(v_stop_1789_);
lean_inc(v_start_1788_);
lean_inc_ref(v_array_1787_);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_snd_1770_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; 
v_unused_1947_ = lean_ctor_get(v_snd_1770_, 2);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_snd_1770_, 1);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_snd_1770_, 0);
lean_dec(v_unused_1949_);
v___x_1809_ = v_snd_1770_;
v_isShared_1810_ = v_isSharedCheck_1946_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_snd_1770_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1946_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_a_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v_a_1811_ = lean_array_uget_borrowed(v_as_1742_, v_i_1744_);
v___x_1812_ = lean_array_fget(v_array_1787_, v_start_1788_);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_add(v_start_1788_, v___x_1813_);
lean_dec(v_start_1788_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1814_);
v___x_1816_ = v___x_1809_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_array_1787_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_stop_1789_);
v___x_1816_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v_proof_1820_; lean_object* v_subst_1821_; uint8_t v___x_1847_; 
lean_inc(v_a_1811_);
v___x_1817_ = l_Lean_Expr_app___override(v_fst_1771_, v_a_1811_);
v___x_1818_ = l_Lean_Expr_bindingBody_x21(v_fst_1775_);
lean_dec(v_fst_1775_);
v___x_1847_ = lean_unbox(v___x_1812_);
lean_dec(v___x_1812_);
switch(v___x_1847_)
{
case 0:
{
lean_del_object(v___x_1785_);
lean_del_object(v___x_1781_);
lean_del_object(v___x_1777_);
lean_del_object(v___x_1773_);
lean_del_object(v___x_1765_);
goto v___jp_1840_;
}
case 3:
{
lean_del_object(v___x_1785_);
lean_del_object(v___x_1781_);
lean_del_object(v___x_1777_);
lean_del_object(v___x_1773_);
lean_del_object(v___x_1765_);
goto v___jp_1840_;
}
case 5:
{
lean_object* v___x_1848_; lean_object* v_instNew_1850_; lean_object* v___x_1859_; 
lean_del_object(v___x_1785_);
lean_del_object(v___x_1781_);
lean_del_object(v___x_1777_);
lean_del_object(v___x_1773_);
lean_del_object(v___x_1765_);
lean_inc_n(v_a_1811_, 2);
v___x_1848_ = lean_array_push(v_fst_1783_, v_a_1811_);
v___x_1859_ = l_Lean_Meta_Sym_inferType___redArg(v_a_1811_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = l_Lean_Expr_bindingDomain_x21(v___x_1818_);
v___x_1862_ = lean_expr_instantiate_rev(v___x_1861_, v___x_1848_);
lean_dec_ref(v___x_1861_);
lean_inc_ref(v___x_1862_);
v___x_1863_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_1860_, v___x_1862_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; uint8_t v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = lean_unbox(v_a_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Meta_trySynthInstance(v___x_1862_, v___x_1790_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1884_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1884_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1884_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
if (lean_obj_tag(v_a_1867_) == 1)
{
lean_object* v_a_1871_; 
lean_del_object(v___x_1869_);
lean_dec(v_a_1864_);
v_a_1871_ = lean_ctor_get(v_a_1867_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v_a_1867_);
v_instNew_1850_ = v_a_1871_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec(v_a_1867_);
v___x_1872_ = lean_alloc_ctor(0, 0, 2);
v___x_1873_ = lean_unbox(v_a_1864_);
lean_ctor_set_uint8(v___x_1872_, 0, v___x_1873_);
v___x_1874_ = lean_unbox(v_a_1864_);
lean_dec(v_a_1864_);
lean_ctor_set_uint8(v___x_1872_, 1, v___x_1874_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1872_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1848_);
lean_ctor_set(v___x_1876_, 1, v___x_1816_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_fst_1779_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1818_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1817_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1875_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1880_);
v___x_1882_ = v___x_1869_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1864_);
lean_dec_ref(v___x_1848_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1816_);
lean_dec(v_fst_1779_);
v_a_1885_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1866_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1866_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_dec(v_a_1864_);
lean_dec_ref(v___x_1862_);
lean_inc(v_a_1811_);
v_instNew_1850_ = v_a_1811_;
goto v___jp_1849_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v___x_1862_);
lean_dec_ref(v___x_1848_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1816_);
lean_dec(v_fst_1779_);
v_a_1893_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1863_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1863_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v___x_1848_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1816_);
lean_dec(v_fst_1779_);
v_a_1901_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1859_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1859_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
v___jp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_inc_ref(v_instNew_1850_);
v___x_1851_ = l_Lean_Expr_app___override(v___x_1817_, v_instNew_1850_);
v___x_1852_ = lean_array_push(v___x_1848_, v_instNew_1850_);
v___x_1853_ = l_Lean_Expr_bindingBody_x21(v___x_1818_);
lean_dec_ref(v___x_1818_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1816_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_fst_1779_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1853_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1851_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1790_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v_a_1757_ = v___x_1858_;
goto v___jp_1756_;
}
}
case 2:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1811_);
v___x_1910_ = lean_array_push(v_fst_1783_, v_a_1811_);
v___x_1911_ = lean_array_get_borrowed(v___x_1909_, v_argResults_1741_, v_fst_1779_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1912_; 
lean_inc(v_a_1811_);
v___x_1912_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_1811_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_n(v_a_1913_, 2);
lean_dec_ref(v___x_1912_);
lean_inc_n(v_a_1811_, 2);
v___x_1914_ = l_Lean_mkAppB(v___x_1817_, v_a_1811_, v_a_1913_);
v___x_1915_ = lean_array_push(v___x_1910_, v_a_1811_);
v___x_1916_ = lean_array_push(v___x_1915_, v_a_1913_);
v_proof_1820_ = v___x_1914_;
v_subst_1821_ = v___x_1916_;
goto v___jp_1819_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v___x_1910_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1816_);
lean_del_object(v___x_1785_);
lean_del_object(v___x_1781_);
lean_dec(v_fst_1779_);
lean_del_object(v___x_1777_);
lean_del_object(v___x_1773_);
lean_del_object(v___x_1765_);
v_a_1917_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1912_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1912_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_e_x27_1925_; lean_object* v_proof_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_e_x27_1925_ = lean_ctor_get(v___x_1911_, 0);
v_proof_1926_ = lean_ctor_get(v___x_1911_, 1);
lean_inc_ref_n(v_proof_1926_, 2);
lean_inc_ref_n(v_e_x27_1925_, 2);
v___x_1927_ = l_Lean_mkAppB(v___x_1817_, v_e_x27_1925_, v_proof_1926_);
v___x_1928_ = lean_array_push(v___x_1910_, v_e_x27_1925_);
v___x_1929_ = lean_array_push(v___x_1928_, v_proof_1926_);
v_proof_1820_ = v___x_1927_;
v_subst_1821_ = v___x_1929_;
goto v___jp_1819_;
}
}
default: 
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_del_object(v___x_1785_);
lean_del_object(v___x_1781_);
lean_del_object(v___x_1777_);
lean_del_object(v___x_1773_);
lean_del_object(v___x_1765_);
v___x_1930_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
v___x_1931_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_1930_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v___x_1931_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_fst_1783_);
lean_ctor_set(v___x_1932_, 1, v___x_1816_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_fst_1779_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1818_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1817_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1790_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v_a_1757_ = v___x_1936_;
goto v___jp_1756_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1816_);
lean_dec(v_fst_1783_);
lean_dec(v_fst_1779_);
v_a_1937_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1931_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1931_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
v___jp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1822_ = l_Lean_Expr_bindingBody_x21(v___x_1818_);
lean_dec_ref(v___x_1818_);
v___x_1823_ = l_Lean_Expr_bindingBody_x21(v___x_1822_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_nat_add(v_fst_1779_, v___x_1813_);
lean_dec(v_fst_1779_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1816_);
lean_ctor_set(v___x_1785_, 0, v_subst_1821_);
v___x_1826_ = v___x_1785_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_subst_1821_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1816_);
v___x_1826_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 1, v___x_1826_);
lean_ctor_set(v___x_1781_, 0, v___x_1824_);
v___x_1828_ = v___x_1781_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v___x_1828_);
lean_ctor_set(v___x_1777_, 0, v___x_1823_);
v___x_1830_ = v___x_1777_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1830_);
lean_ctor_set(v___x_1773_, 0, v_proof_1820_);
v___x_1832_ = v___x_1773_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_proof_1820_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1832_);
lean_ctor_set(v___x_1765_, 0, v___x_1790_);
v___x_1834_ = v___x_1765_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v_a_1757_ = v___x_1834_;
goto v___jp_1756_;
}
}
}
}
}
}
v___jp_1840_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_inc(v_a_1811_);
v___x_1841_ = lean_array_push(v_fst_1783_, v_a_1811_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1816_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_fst_1779_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1818_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1817_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1790_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v_a_1757_ = v___x_1846_;
goto v___jp_1756_;
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
v___jp_1756_:
{
size_t v___x_1758_; size_t v___x_1759_; 
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1744_, v___x_1758_);
v_i_1744_ = v___x_1759_;
v_b_1745_ = v_a_1757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_1960_, lean_object* v_as_1961_, lean_object* v_sz_1962_, lean_object* v_i_1963_, lean_object* v_b_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
size_t v_sz_boxed_1975_; size_t v_i_boxed_1976_; lean_object* v_res_1977_; 
v_sz_boxed_1975_ = lean_unbox_usize(v_sz_1962_);
lean_dec(v_sz_1962_);
v_i_boxed_1976_ = lean_unbox_usize(v_i_1963_);
lean_dec(v_i_1963_);
v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1960_, v_as_1961_, v_sz_boxed_1975_, v_i_boxed_1976_, v_b_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v_as_1961_);
lean_dec_ref(v_argResults_1960_);
return v_res_1977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1979_ = lean_unsigned_to_nat(34u);
v___x_1980_ = lean_unsigned_to_nat(402u);
v___x_1981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1982_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1983_ = l_mkPanicMessageWithDecl(v___x_1982_, v___x_1981_, v___x_1980_, v___x_1979_, v___x_1978_);
return v___x_1983_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1986_; lean_object* v_dummy_1987_; 
v___x_1986_ = lean_box(0);
v_dummy_1987_ = l_Lean_Expr_sort___override(v___x_1986_);
return v_dummy_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_1991_, lean_object* v_argKinds_1992_, lean_object* v_type_1993_, lean_object* v_proof_1994_, lean_object* v_argResults_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v_j_2018_; lean_object* v_subst_2019_; lean_object* v_dummy_2020_; lean_object* v_nargs_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_args_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; size_t v_sz_2034_; size_t v___x_2035_; lean_object* v___x_2036_; 
v_j_2018_ = lean_unsigned_to_nat(0u);
v_subst_2019_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2020_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2021_ = l_Lean_Expr_getAppNumArgs(v_e_1991_);
lean_inc(v_nargs_2021_);
v___x_2022_ = lean_mk_array(v_nargs_2021_, v_dummy_2020_);
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_sub(v_nargs_2021_, v___x_2023_);
lean_dec(v_nargs_2021_);
v_args_2025_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1991_, v___x_2022_, v___x_2024_);
v___x_2026_ = lean_array_get_size(v_argKinds_1992_);
lean_inc_ref(v_argKinds_1992_);
v___x_2027_ = l_Array_toSubarray___redArg(v_argKinds_1992_, v_j_2018_, v___x_2026_);
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_subst_2019_);
lean_ctor_set(v___x_2029_, 1, v___x_2027_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_j_2018_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_type_1993_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_proof_1994_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v_sz_2034_ = lean_array_size(v_args_2025_);
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1995_, v_args_2025_, v_sz_2034_, v___x_2035_, v___x_2033_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec_ref(v_args_2025_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2102_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2102_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2102_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_fst_2041_; 
v_fst_2041_ = lean_ctor_get(v_a_2037_, 0);
if (lean_obj_tag(v_fst_2041_) == 0)
{
lean_object* v_snd_2042_; lean_object* v_fst_2043_; lean_object* v_snd_2044_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v_rhs_2054_; lean_object* v___y_2055_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_snd_2042_ = lean_ctor_get(v_a_2037_, 1);
lean_inc(v_snd_2042_);
lean_dec(v_a_2037_);
v_fst_2043_ = lean_ctor_get(v_snd_2042_, 0);
lean_inc(v_fst_2043_);
v_snd_2044_ = lean_ctor_get(v_snd_2042_, 1);
lean_inc(v_snd_2044_);
lean_dec(v_snd_2042_);
v_fst_2070_ = lean_ctor_get(v_snd_2044_, 0);
lean_inc(v_fst_2070_);
v_snd_2071_ = lean_ctor_get(v_snd_2044_, 1);
lean_inc(v_snd_2071_);
lean_dec(v_snd_2044_);
v___x_2072_ = l_Lean_Expr_cleanupAnnotations(v_fst_2070_);
v___x_2073_ = l_Lean_Expr_isApp(v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v___x_2072_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2043_);
lean_del_object(v___x_2039_);
lean_dec_ref(v_argKinds_1992_);
v___y_2007_ = v___y_1996_;
v___y_2008_ = v___y_1997_;
v___y_2009_ = v___y_1998_;
v___y_2010_ = v___y_1999_;
v___y_2011_ = v___y_2000_;
v___y_2012_ = v___y_2001_;
v___y_2013_ = v___y_2002_;
v___y_2014_ = v___y_2003_;
v___y_2015_ = v___y_2004_;
goto v___jp_2006_;
}
else
{
lean_object* v_arg_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_arg_2074_ = lean_ctor_get(v___x_2072_, 1);
lean_inc_ref(v_arg_2074_);
v___x_2075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2072_);
v___x_2076_ = l_Lean_Expr_isApp(v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_arg_2074_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2043_);
lean_del_object(v___x_2039_);
lean_dec_ref(v_argKinds_1992_);
v___y_2007_ = v___y_1996_;
v___y_2008_ = v___y_1997_;
v___y_2009_ = v___y_1998_;
v___y_2010_ = v___y_1999_;
v___y_2011_ = v___y_2000_;
v___y_2012_ = v___y_2001_;
v___y_2013_ = v___y_2002_;
v___y_2014_ = v___y_2003_;
v___y_2015_ = v___y_2004_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2075_);
v___x_2078_ = l_Lean_Expr_isApp(v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec_ref(v___x_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2043_);
lean_del_object(v___x_2039_);
lean_dec_ref(v_argKinds_1992_);
v___y_2007_ = v___y_1996_;
v___y_2008_ = v___y_1997_;
v___y_2009_ = v___y_1998_;
v___y_2010_ = v___y_1999_;
v___y_2011_ = v___y_2000_;
v___y_2012_ = v___y_2001_;
v___y_2013_ = v___y_2002_;
v___y_2014_ = v___y_2003_;
v___y_2015_ = v___y_2004_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2077_);
v___x_2080_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2081_ = l_Lean_Expr_isConstOf(v___x_2079_, v___x_2080_);
lean_dec_ref(v___x_2079_);
if (v___x_2081_ == 0)
{
lean_dec_ref(v_arg_2074_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2043_);
lean_del_object(v___x_2039_);
lean_dec_ref(v_argKinds_1992_);
v___y_2007_ = v___y_1996_;
v___y_2008_ = v___y_1997_;
v___y_2009_ = v___y_1998_;
v___y_2010_ = v___y_1999_;
v___y_2011_ = v___y_2000_;
v___y_2012_ = v___y_2001_;
v___y_2013_ = v___y_2002_;
v___y_2014_ = v___y_2003_;
v___y_2015_ = v___y_2004_;
goto v___jp_2006_;
}
else
{
lean_object* v_snd_2082_; lean_object* v_fst_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_snd_2082_ = lean_ctor_get(v_snd_2071_, 1);
lean_inc(v_snd_2082_);
lean_dec(v_snd_2071_);
v_fst_2083_ = lean_ctor_get(v_snd_2082_, 0);
lean_inc(v_fst_2083_);
lean_dec(v_snd_2082_);
v___x_2084_ = lean_expr_instantiate_rev(v_arg_2074_, v_fst_2083_);
lean_dec(v_fst_2083_);
lean_dec_ref(v_arg_2074_);
v___x_2085_ = lean_nat_dec_lt(v_j_2018_, v___x_2026_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v_argKinds_1992_);
v_rhs_2054_ = v___x_2084_;
v___y_2055_ = v___y_2000_;
goto v___jp_2053_;
}
else
{
if (v___x_2085_ == 0)
{
lean_dec_ref(v_argKinds_1992_);
v_rhs_2054_ = v___x_2084_;
v___y_2055_ = v___y_2000_;
goto v___jp_2053_;
}
else
{
size_t v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_usize_of_nat(v___x_2026_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_2081_, v_argKinds_1992_, v___x_2035_, v___x_2086_);
lean_dec_ref(v_argKinds_1992_);
if (v___x_2087_ == 0)
{
v_rhs_2054_ = v___x_2084_;
v___y_2055_ = v___y_2000_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2084_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2088_);
v_rhs_2054_ = v_a_2089_;
v___y_2055_ = v___y_2000_;
goto v___jp_2053_;
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_fst_2043_);
lean_del_object(v___x_2039_);
v_a_2090_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2088_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2088_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
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
v___jp_2045_:
{
uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2048_ = 0;
v___x_2049_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2049_, 0, v___y_2046_);
lean_ctor_set(v___x_2049_, 1, v_fst_2043_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*2, v___x_2048_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*2 + 1, v___y_2047_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2049_);
v___x_2051_ = v___x_2039_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
v___jp_2053_:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_rhs_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = lean_array_get_size(v_argResults_1995_);
v___x_2059_ = lean_nat_dec_lt(v_j_2018_, v___x_2058_);
if (v___x_2059_ == 0)
{
v___y_2046_ = v_a_2057_;
v___y_2047_ = v___x_2059_;
goto v___jp_2045_;
}
else
{
if (v___x_2059_ == 0)
{
v___y_2046_ = v_a_2057_;
v___y_2047_ = v___x_2059_;
goto v___jp_2045_;
}
else
{
size_t v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = lean_usize_of_nat(v___x_2058_);
v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_1995_, v___x_2035_, v___x_2060_);
v___y_2046_ = v_a_2057_;
v___y_2047_ = v___x_2061_;
goto v___jp_2045_;
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_fst_2043_);
lean_del_object(v___x_2039_);
v_a_2062_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2056_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2056_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2100_; 
lean_inc_ref(v_fst_2041_);
lean_dec(v_a_2037_);
lean_dec_ref(v_argKinds_1992_);
v_val_2098_ = lean_ctor_get(v_fst_2041_, 0);
lean_inc(v_val_2098_);
lean_dec_ref(v_fst_2041_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v_val_2098_);
v___x_2100_ = v___x_2039_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_val_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v_argKinds_1992_);
v_a_2103_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2036_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2036_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
v___jp_2006_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_2017_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2016_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2111_, lean_object* v_argKinds_2112_, lean_object* v_type_2113_, lean_object* v_proof_2114_, lean_object* v_argResults_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2111_, v_argKinds_2112_, v_type_2113_, v_proof_2114_, v_argResults_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v_argResults_2115_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2127_, lean_object* v_x_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2139_, 0, v___x_2127_);
lean_ctor_set_uint8(v___x_2139_, 1, v___x_2127_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2141_, lean_object* v_x_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v___x_24024__boxed_2153_; lean_object* v_res_2154_; 
v___x_24024__boxed_2153_ = lean_unbox(v___x_2141_);
v_res_2154_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_24024__boxed_2153_, v_x_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v_x_2142_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2157_, lean_object* v_argKinds_2158_, lean_object* v_mkNonRflResult_2159_, lean_object* v_x_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_sub(v___x_2157_, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2175_ = 0;
v___x_2176_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2158_, v_mkNonRflResult_2159_, v_x_2160_, v___x_2172_, v___x_2173_, v___x_2174_, v___x_2175_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2177_, lean_object* v_argKinds_2178_, lean_object* v_mkNonRflResult_2179_, lean_object* v_x_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2177_, v_argKinds_2178_, v_mkNonRflResult_2179_, v_x_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v_argKinds_2178_);
lean_dec(v___x_2177_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2192_, lean_object* v_thm_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_type_2204_; lean_object* v_proof_2205_; lean_object* v_argKinds_2206_; lean_object* v_mkNonRflResult_2207_; lean_object* v_numArgs_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_type_2204_ = lean_ctor_get(v_thm_2193_, 0);
lean_inc_ref(v_type_2204_);
v_proof_2205_ = lean_ctor_get(v_thm_2193_, 1);
lean_inc_ref(v_proof_2205_);
v_argKinds_2206_ = lean_ctor_get(v_thm_2193_, 2);
lean_inc_ref_n(v_argKinds_2206_, 2);
lean_dec_ref(v_thm_2193_);
lean_inc_ref(v_e_2192_);
v_mkNonRflResult_2207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2207_, 0, v_e_2192_);
lean_closure_set(v_mkNonRflResult_2207_, 1, v_argKinds_2206_);
lean_closure_set(v_mkNonRflResult_2207_, 2, v_type_2204_);
lean_closure_set(v_mkNonRflResult_2207_, 3, v_proof_2205_);
v_numArgs_2208_ = l_Lean_Expr_getAppNumArgs(v_e_2192_);
v___x_2209_ = lean_array_get_size(v_argKinds_2206_);
v___x_2210_ = lean_nat_dec_lt(v___x_2209_, v_numArgs_2208_);
if (v___x_2210_ == 0)
{
uint8_t v___x_2211_; 
v___x_2211_ = lean_nat_dec_lt(v_numArgs_2208_, v___x_2209_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_numArgs_2208_);
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_sub(v___x_2209_, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2216_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2206_, v_mkNonRflResult_2207_, v_e_2192_, v___x_2213_, v___x_2214_, v___x_2215_, v___x_2211_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec_ref(v_argKinds_2206_);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v_mkNonRflResult_2207_);
lean_dec_ref(v_argKinds_2206_);
v___x_2217_ = lean_box(v___x_2210_);
v___f_2218_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2218_, 0, v___x_2217_);
v___x_2219_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2218_, v_e_2192_, v_numArgs_2208_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_numArgs_2208_);
return v___x_2219_;
}
}
else
{
lean_object* v___f_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___f_2220_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2220_, 0, v___x_2209_);
lean_closure_set(v___f_2220_, 1, v_argKinds_2206_);
lean_closure_set(v___f_2220_, 2, v_mkNonRflResult_2207_);
v___x_2221_ = lean_nat_sub(v_numArgs_2208_, v___x_2209_);
lean_dec(v_numArgs_2208_);
v___x_2222_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2220_, v_e_2192_, v___x_2221_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v___x_2221_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2223_, lean_object* v_thm_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2223_, v_thm_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_f_2247_; lean_object* v___x_2248_; 
v_f_2247_ = l_Lean_Expr_getAppFn(v_e_2236_);
v___x_2248_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2247_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2264_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2264_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2264_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
switch(lean_obj_tag(v_a_2249_))
{
case 0:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
lean_dec_ref(v_e_2236_);
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
case 1:
{
lean_object* v_prefixSize_2257_; lean_object* v_suffixSize_2258_; lean_object* v___x_2259_; 
lean_del_object(v___x_2251_);
v_prefixSize_2257_ = lean_ctor_get(v_a_2249_, 0);
lean_inc(v_prefixSize_2257_);
v_suffixSize_2258_ = lean_ctor_get(v_a_2249_, 1);
lean_inc(v_suffixSize_2258_);
lean_dec_ref(v_a_2249_);
v___x_2259_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2236_, v_prefixSize_2257_, v_suffixSize_2258_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_prefixSize_2257_);
return v___x_2259_;
}
case 2:
{
lean_object* v_rewritable_2260_; lean_object* v___x_2261_; 
lean_del_object(v___x_2251_);
v_rewritable_2260_ = lean_ctor_get(v_a_2249_, 0);
lean_inc_ref(v_rewritable_2260_);
lean_dec_ref(v_a_2249_);
v___x_2261_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2236_, v_rewritable_2260_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v___x_2261_;
}
default: 
{
lean_object* v_thm_2262_; lean_object* v___x_2263_; 
lean_del_object(v___x_2251_);
v_thm_2262_ = lean_ctor_get(v_a_2249_, 0);
lean_inc_ref(v_thm_2262_);
lean_dec_ref(v_a_2249_);
v___x_2263_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2236_, v_thm_2262_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v_e_2236_);
v_a_2265_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2248_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2248_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
return v_res_2284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2287_ = lean_unsigned_to_nat(55u);
v___x_2288_ = lean_unsigned_to_nat(489u);
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2290_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2291_ = l_mkPanicMessageWithDecl(v___x_2290_, v___x_2289_, v___x_2288_, v___x_2287_, v___x_2286_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2293_ = lean_unsigned_to_nat(11u);
v___x_2294_ = lean_unsigned_to_nat(497u);
v___x_2295_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2297_ = l_mkPanicMessageWithDecl(v___x_2296_, v___x_2295_, v___x_2294_, v___x_2293_, v___x_2292_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2298_, lean_object* v_e_2299_, lean_object* v_i_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
uint8_t v_cd_2312_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_nat_dec_eq(v_i_2300_, v___x_2315_);
if (v___x_2316_ == 0)
{
if (lean_obj_tag(v_e_2299_) == 5)
{
lean_object* v_fn_2317_; lean_object* v_arg_2318_; lean_object* v___x_2319_; lean_object* v_i_2320_; lean_object* v___x_2321_; 
v_fn_2317_ = lean_ctor_get(v_e_2299_, 0);
lean_inc_ref_n(v_fn_2317_, 2);
v_arg_2318_ = lean_ctor_get(v_e_2299_, 1);
lean_inc_ref(v_arg_2318_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v_i_2320_ = lean_nat_sub(v_i_2300_, v___x_2319_);
v___x_2321_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2298_, v_fn_2317_, v_i_2320_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; uint8_t v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = lean_nat_dec_lt(v_i_2320_, v_stop_2298_);
lean_dec(v_i_2320_);
if (v___x_2323_ == 0)
{
if (lean_obj_tag(v_a_2322_) == 0)
{
uint8_t v_contextDependent_2324_; 
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
v_contextDependent_2324_ = lean_ctor_get_uint8(v_a_2322_, 1);
lean_dec_ref(v_a_2322_);
v_cd_2312_ = v_contextDependent_2324_;
goto v___jp_2311_;
}
else
{
lean_object* v_e_x27_2325_; lean_object* v_proof_2326_; uint8_t v_contextDependent_2327_; lean_object* v___x_2328_; 
v_e_x27_2325_ = lean_ctor_get(v_a_2322_, 0);
lean_inc_ref(v_e_x27_2325_);
v_proof_2326_ = lean_ctor_get(v_a_2322_, 1);
lean_inc_ref(v_proof_2326_);
v_contextDependent_2327_ = lean_ctor_get_uint8(v_a_2322_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_2322_);
v___x_2328_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2299_, v_fn_2317_, v_arg_2318_, v_e_x27_2325_, v_proof_2326_, v___x_2316_, v_contextDependent_2327_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2328_;
}
}
else
{
lean_object* v___x_2329_; 
lean_inc_ref(v_fn_2317_);
v___x_2329_ = l_Lean_Meta_Sym_inferType___redArg(v_fn_2317_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l_Lean_Meta_whnfD(v_a_2330_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
if (lean_obj_tag(v_a_2332_) == 7)
{
lean_object* v_binderType_2333_; lean_object* v_body_2334_; uint8_t v___x_2352_; 
v_binderType_2333_ = lean_ctor_get(v_a_2332_, 1);
lean_inc_ref(v_binderType_2333_);
v_body_2334_ = lean_ctor_get(v_a_2332_, 2);
lean_inc_ref(v_body_2334_);
lean_dec_ref(v_a_2332_);
v___x_2352_ = l_Lean_Expr_hasLooseBVars(v_body_2334_);
lean_dec_ref(v_body_2334_);
if (v___x_2352_ == 0)
{
goto v___jp_2335_;
}
else
{
if (v___x_2316_ == 0)
{
lean_dec_ref(v_binderType_2333_);
if (lean_obj_tag(v_a_2322_) == 0)
{
uint8_t v_contextDependent_2353_; 
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
v_contextDependent_2353_ = lean_ctor_get_uint8(v_a_2322_, 1);
lean_dec_ref(v_a_2322_);
v_cd_2312_ = v_contextDependent_2353_;
goto v___jp_2311_;
}
else
{
lean_object* v_e_x27_2354_; lean_object* v_proof_2355_; uint8_t v_contextDependent_2356_; lean_object* v___x_2357_; 
v_e_x27_2354_ = lean_ctor_get(v_a_2322_, 0);
lean_inc_ref(v_e_x27_2354_);
v_proof_2355_ = lean_ctor_get(v_a_2322_, 1);
lean_inc_ref(v_proof_2355_);
v_contextDependent_2356_ = lean_ctor_get_uint8(v_a_2322_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_2322_);
v___x_2357_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2299_, v_fn_2317_, v_arg_2318_, v_e_x27_2354_, v_proof_2355_, v___x_2316_, v_contextDependent_2356_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2357_;
}
}
else
{
goto v___jp_2335_;
}
}
v___jp_2335_:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Meta_isProp(v_binderType_2333_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref(v___x_2336_);
v___x_2338_ = lean_unbox(v_a_2337_);
lean_dec(v_a_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
lean_inc(v_a_2309_);
lean_inc_ref(v_a_2308_);
lean_inc(v_a_2307_);
lean_inc_ref(v_a_2306_);
lean_inc(v_a_2305_);
lean_inc_ref(v_a_2304_);
lean_inc(v_a_2303_);
lean_inc_ref(v_a_2302_);
lean_inc(v_a_2301_);
lean_inc_ref(v_arg_2318_);
v___x_2339_ = lean_sym_simp(v_arg_2318_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2299_, v_fn_2317_, v_arg_2318_, v_a_2322_, v_a_2340_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2341_;
}
else
{
lean_dec(v_a_2322_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
return v___x_2339_;
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2342_, 0, v___x_2316_);
lean_ctor_set_uint8(v___x_2342_, 1, v___x_2316_);
v___x_2343_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2299_, v_fn_2317_, v_arg_2318_, v_a_2322_, v___x_2342_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2343_;
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_a_2322_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
v_a_2344_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2336_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2336_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_a_2332_);
lean_dec(v_a_2322_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
v___x_2358_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2359_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2358_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2359_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2322_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
v_a_2360_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2331_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2331_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2322_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
v_a_2368_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2329_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2329_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
lean_dec(v_i_2320_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
lean_dec_ref(v_e_2299_);
return v___x_2321_;
}
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec_ref(v_e_2299_);
v___x_2376_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2377_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2376_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2377_;
}
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_e_2299_);
v___x_2378_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_2312_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2380_, lean_object* v_e_2381_, lean_object* v_i_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2380_, v_e_2381_, v_i_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec(v_i_2382_);
lean_dec(v_stop_2380_);
return v_res_2393_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2397_ = lean_unsigned_to_nat(2u);
v___x_2398_ = lean_unsigned_to_nat(472u);
v___x_2399_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2401_ = l_mkPanicMessageWithDecl(v___x_2400_, v___x_2399_, v___x_2398_, v___x_2397_, v___x_2396_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2402_, lean_object* v_start_2403_, lean_object* v_stop_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
uint8_t v___x_2415_; 
v___x_2415_ = lean_nat_dec_lt(v_start_2403_, v_stop_2404_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec_ref(v_e_2402_);
v___x_2416_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2417_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2416_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2417_;
}
else
{
lean_object* v_numArgs_2418_; uint8_t v___x_2419_; 
v_numArgs_2418_ = l_Lean_Expr_getAppNumArgs(v_e_2402_);
v___x_2419_ = lean_nat_dec_lt(v_numArgs_2418_, v_start_2403_);
if (v___x_2419_ == 0)
{
lean_object* v_numArgs_2420_; lean_object* v_stop_2421_; lean_object* v___x_2422_; 
v_numArgs_2420_ = lean_nat_sub(v_numArgs_2418_, v_start_2403_);
lean_dec(v_numArgs_2418_);
v_stop_2421_ = lean_nat_sub(v_stop_2404_, v_start_2403_);
v___x_2422_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2421_, v_e_2402_, v_numArgs_2420_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_numArgs_2420_);
lean_dec(v_stop_2421_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v_numArgs_2418_);
lean_dec_ref(v_e_2402_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2425_, lean_object* v_start_2426_, lean_object* v_stop_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2425_, v_start_2426_, v_stop_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec(v_stop_2427_);
lean_dec(v_start_2426_);
return v_res_2438_;
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
