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
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "function type expected"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1;
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
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*11);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref_known(v___x_16_, 1);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref_known(v___x_17_, 1);
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
v___x_54_ = l_Lean_Meta_Sym_inferType(v_a_44_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_n(v_a_55_, 2);
lean_dec_ref_known(v___x_54_, 1);
v___x_56_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_55_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_56_, 1);
v___x_58_ = l_Lean_Meta_Sym_inferType(v_e_45_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc_n(v_a_59_, 2);
lean_dec_ref_known(v___x_58_, 1);
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
lean_dec_ref_known(v_fr_113_, 0);
if (v_contextDependent_126_ == 0)
{
uint8_t v_contextDependent_127_; 
v_contextDependent_127_ = lean_ctor_get_uint8(v_ar_114_, 1);
lean_dec_ref_known(v_ar_114_, 0);
v___y_123_ = v_contextDependent_127_;
goto v___jp_122_;
}
else
{
lean_dec_ref_known(v_ar_114_, 0);
v___y_123_ = v_contextDependent_126_;
goto v___jp_122_;
}
}
else
{
uint8_t v_contextDependent_128_; lean_object* v_e_x27_129_; lean_object* v_proof_130_; uint8_t v_contextDependent_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_170_; 
v_contextDependent_128_ = lean_ctor_get_uint8(v_fr_113_, 1);
lean_dec_ref_known(v_fr_113_, 0);
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
lean_dec_ref_known(v___x_135_, 1);
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
lean_dec_ref_known(v_ar_114_, 0);
lean_inc_ref(v_a_112_);
lean_inc_ref(v_e_x27_171_);
v___x_178_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_171_, v_a_112_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
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
lean_dec_ref_known(v_fr_113_, 2);
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
lean_dec_ref_known(v___x_223_, 1);
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
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_toCold_309_; lean_object* v_mctx_310_; lean_object* v_lctx_311_; lean_object* v_options_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_302_);
v_toCold_309_ = lean_ctor_get(v___y_303_, 0);
v_mctx_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_310_);
lean_dec(v___x_308_);
v_lctx_311_ = lean_ctor_get(v___y_301_, 2);
v_options_312_ = lean_ctor_get(v_toCold_309_, 2);
lean_inc_ref(v_options_312_);
lean_inc_ref(v_lctx_311_);
v___x_313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_313_, 0, v_env_307_);
lean_ctor_set(v___x_313_, 1, v_mctx_310_);
lean_ctor_set(v___x_313_, 2, v_lctx_311_);
lean_ctor_set(v___x_313_, 3, v_options_312_);
v___x_314_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_msgData_300_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_ref_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_339_; 
v_ref_329_ = lean_ctor_get(v___y_326_, 2);
v___x_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
lean_inc(v_ref_329_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_ref_329_);
lean_ctor_set(v___x_335_, 1, v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 1);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* v_e_353_, lean_object* v_f_354_, lean_object* v_a_355_, lean_object* v_f_x27_356_, lean_object* v_hf_357_, uint8_t v_done_358_, uint8_t v_contextDependent_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
lean_inc_ref(v_f_354_);
v___x_367_ = l_Lean_Meta_Sym_inferType(v_f_354_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = l_Lean_Meta_whnfD(v_a_368_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
if (lean_obj_tag(v_a_370_) == 7)
{
lean_object* v_binderName_371_; lean_object* v_body_372_; lean_object* v___x_373_; 
v_binderName_371_ = lean_ctor_get(v_a_370_, 0);
lean_inc(v_binderName_371_);
v_body_372_ = lean_ctor_get(v_a_370_, 2);
lean_inc_ref(v_body_372_);
lean_dec_ref_known(v_a_370_, 3);
lean_inc_ref(v_a_355_);
v___x_373_ = l_Lean_Meta_Sym_inferType(v_a_355_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc_n(v_a_374_, 2);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_374_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
v___x_377_ = l_Lean_Meta_Sym_inferType(v_e_353_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v___x_377_, 1);
v___x_379_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_378_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
lean_inc_ref(v_a_355_);
lean_inc_ref(v_f_x27_356_);
v___x_381_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_x27_356_, v_a_355_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_398_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_386_ = 0;
lean_inc(v_a_374_);
v___x_387_ = l_Lean_mkLambda(v_binderName_371_, v___x_386_, v_a_374_, v_body_372_);
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v_a_380_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v_a_376_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_mkConst(v___x_388_, v___x_391_);
v___x_393_ = l_Lean_mkApp6(v___x_392_, v_a_374_, v___x_387_, v_f_354_, v_f_x27_356_, v_hf_357_, v_a_355_);
v___x_394_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_394_, 0, v_a_382_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*2, v_done_358_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*2 + 1, v_contextDependent_359_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_394_);
v___x_396_ = v___x_384_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_380_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec_ref(v_body_372_);
lean_dec(v_binderName_371_);
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
v_a_399_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_381_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_381_);
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
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec_ref(v_body_372_);
lean_dec(v_binderName_371_);
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
v_a_407_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_379_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_379_);
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
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec_ref(v_body_372_);
lean_dec(v_binderName_371_);
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
v_a_415_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_377_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_377_);
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
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v_a_374_);
lean_dec_ref(v_body_372_);
lean_dec(v_binderName_371_);
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
lean_dec_ref(v_e_353_);
v_a_423_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_375_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_375_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v_body_372_);
lean_dec(v_binderName_371_);
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
lean_dec_ref(v_e_353_);
v_a_431_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_373_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_373_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_a_370_);
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_e_353_);
v___x_439_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
v___x_440_ = l_Lean_indentExpr(v_f_354_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_441_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_442_;
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
lean_dec_ref(v_e_353_);
v_a_443_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_369_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_369_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_hf_357_);
lean_dec_ref(v_f_x27_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_f_354_);
lean_dec_ref(v_e_353_);
v_a_451_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_367_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_367_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* v_e_459_, lean_object* v_f_460_, lean_object* v_a_461_, lean_object* v_f_x27_462_, lean_object* v_hf_463_, lean_object* v_done_464_, lean_object* v_contextDependent_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
uint8_t v_done_boxed_473_; uint8_t v_contextDependent_boxed_474_; lean_object* v_res_475_; 
v_done_boxed_473_ = lean_unbox(v_done_464_);
v_contextDependent_boxed_474_ = lean_unbox(v_contextDependent_465_);
v_res_475_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_459_, v_f_460_, v_a_461_, v_f_x27_462_, v_hf_463_, v_done_boxed_473_, v_contextDependent_boxed_474_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* v_e_476_, lean_object* v_f_477_, lean_object* v_a_478_, lean_object* v_f_x27_479_, lean_object* v_hf_480_, lean_object* v_x_481_, uint8_t v_done_482_, uint8_t v_contextDependent_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_476_, v_f_477_, v_a_478_, v_f_x27_479_, v_hf_480_, v_done_482_, v_contextDependent_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* v_e_492_, lean_object* v_f_493_, lean_object* v_a_494_, lean_object* v_f_x27_495_, lean_object* v_hf_496_, lean_object* v_x_497_, lean_object* v_done_498_, lean_object* v_contextDependent_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
uint8_t v_done_boxed_507_; uint8_t v_contextDependent_boxed_508_; lean_object* v_res_509_; 
v_done_boxed_507_ = lean_unbox(v_done_498_);
v_contextDependent_boxed_508_ = lean_unbox(v_contextDependent_499_);
v_res_509_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(v_e_492_, v_f_493_, v_a_494_, v_f_x27_495_, v_hf_496_, v_x_497_, v_done_boxed_507_, v_contextDependent_boxed_508_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* v_00_u03b1_510_, lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_511_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* v_00_u03b1_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(v_00_u03b1_520_, v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_529_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_6782__overap_543_; lean_object* v___x_544_; 
v___x_542_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_6782__overap_543_ = lean_panic_fn_borrowed(v___x_542_, v_msg_531_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
v___x_544_ = lean_apply_10(v___x_6782__overap_543_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* v_msg_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
return v_res_556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_561_ = lean_unsigned_to_nat(55u);
v___x_562_ = lean_unsigned_to_nat(127u);
v___x_563_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_564_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_565_ = l_mkPanicMessageWithDecl(v___x_564_, v___x_563_, v___x_562_, v___x_561_, v___x_560_);
return v___x_565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_567_ = lean_unsigned_to_nat(13u);
v___x_568_ = lean_unsigned_to_nat(139u);
v___x_569_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_571_ = l_mkPanicMessageWithDecl(v___x_570_, v___x_569_, v___x_568_, v___x_567_, v___x_566_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* v_simpFn_572_, lean_object* v_e_573_, lean_object* v_i_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_nat_dec_eq(v_i_574_, v___x_585_);
if (v___x_586_ == 0)
{
switch(lean_obj_tag(v_e_573_))
{
case 10:
{
lean_object* v_expr_587_; 
v_expr_587_ = lean_ctor_get(v_e_573_, 1);
lean_inc_ref(v_expr_587_);
lean_dec_ref_known(v_e_573_, 2);
v_e_573_ = v_expr_587_;
goto _start;
}
case 5:
{
lean_object* v_fn_589_; lean_object* v_arg_590_; lean_object* v___x_591_; lean_object* v_i_592_; lean_object* v___x_593_; 
v_fn_589_ = lean_ctor_get(v_e_573_, 0);
lean_inc_ref_n(v_fn_589_, 2);
v_arg_590_ = lean_ctor_get(v_e_573_, 1);
lean_inc_ref(v_arg_590_);
v___x_591_ = lean_unsigned_to_nat(1u);
v_i_592_ = lean_nat_sub(v_i_574_, v___x_591_);
v___x_593_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_572_, v_fn_589_, v_i_592_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_i_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
lean_inc_ref(v_fn_589_);
v___x_595_ = l_Lean_Meta_Sym_inferType(v_fn_589_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = l_Lean_Meta_whnfD(v_a_596_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_632_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_632_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_632_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_632_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
if (lean_obj_tag(v_a_598_) == 7)
{
lean_object* v_binderType_602_; lean_object* v_body_603_; uint8_t v___x_604_; 
v_binderType_602_ = lean_ctor_get(v_a_598_, 1);
lean_inc_ref(v_binderType_602_);
v_body_603_ = lean_ctor_get(v_a_598_, 2);
lean_inc_ref(v_body_603_);
lean_dec_ref_known(v_a_598_, 3);
v___x_604_ = l_Lean_Expr_hasLooseBVars(v_body_603_);
lean_dec_ref(v_body_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_del_object(v___x_600_);
v___x_605_ = l_Lean_Meta_isProp(v_binderType_602_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; uint8_t v___x_607_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 1);
v___x_607_ = lean_unbox(v_a_606_);
lean_dec(v_a_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_inc(v_a_583_);
lean_inc_ref(v_a_582_);
lean_inc(v_a_581_);
lean_inc_ref(v_a_580_);
lean_inc(v_a_579_);
lean_inc_ref(v_a_578_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
lean_inc(v_a_575_);
lean_inc_ref(v_arg_590_);
v___x_608_ = lean_sym_simp(v_arg_590_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_573_, v_fn_589_, v_arg_590_, v_a_594_, v_a_609_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_610_;
}
else
{
lean_dec(v_a_594_);
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
return v___x_608_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_611_, 0, v___x_586_);
lean_ctor_set_uint8(v___x_611_, 1, v___x_586_);
v___x_612_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_573_, v_fn_589_, v_arg_590_, v_a_594_, v___x_611_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_612_;
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_594_);
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
v_a_613_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_605_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_605_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_602_);
if (lean_obj_tag(v_a_594_) == 0)
{
uint8_t v_contextDependent_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
v_contextDependent_621_ = lean_ctor_get_uint8(v_a_594_, 1);
lean_dec_ref_known(v_a_594_, 0);
v___x_622_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_621_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_622_);
v___x_624_ = v___x_600_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v_e_x27_626_; lean_object* v_proof_627_; uint8_t v_contextDependent_628_; lean_object* v___x_629_; 
lean_del_object(v___x_600_);
v_e_x27_626_ = lean_ctor_get(v_a_594_, 0);
lean_inc_ref(v_e_x27_626_);
v_proof_627_ = lean_ctor_get(v_a_594_, 1);
lean_inc_ref(v_proof_627_);
v_contextDependent_628_ = lean_ctor_get_uint8(v_a_594_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_594_, 2);
v___x_629_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_573_, v_fn_589_, v_arg_590_, v_e_x27_626_, v_proof_627_, v___x_586_, v_contextDependent_628_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_629_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
lean_dec(v_a_594_);
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
v___x_630_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
v___x_631_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_630_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_631_;
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_594_);
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
v_a_633_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_597_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_597_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_a_594_);
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
v_a_641_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_595_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_595_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_dec_ref(v_arg_590_);
lean_dec_ref_known(v_e_573_, 2);
lean_dec_ref(v_fn_589_);
return v___x_593_;
}
}
default: 
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref(v_e_573_);
lean_dec_ref(v_simpFn_572_);
v___x_649_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
v___x_650_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_649_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_650_;
}
}
}
else
{
lean_object* v___x_651_; 
lean_inc(v_a_583_);
lean_inc_ref(v_a_582_);
lean_inc(v_a_581_);
lean_inc_ref(v_a_580_);
lean_inc(v_a_579_);
lean_inc_ref(v_a_578_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
lean_inc(v_a_575_);
v___x_651_ = lean_apply_11(v_simpFn_572_, v_e_573_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, lean_box(0));
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* v_simpFn_652_, lean_object* v_e_653_, lean_object* v_i_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_652_, v_e_653_, v_i_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec(v_i_654_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* v_e_666_, lean_object* v_numArgs_667_, lean_object* v_simpFn_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_668_, v_e_666_, v_numArgs_667_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* v_e_680_, lean_object* v_numArgs_681_, lean_object* v_simpFn_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_680_, v_numArgs_681_, v_simpFn_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec(v_numArgs_681_);
return v_res_693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_696_ = lean_unsigned_to_nat(13u);
v___x_697_ = lean_unsigned_to_nat(176u);
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_700_ = l_mkPanicMessageWithDecl(v___x_699_, v___x_698_, v___x_697_, v___x_696_, v___x_695_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* v_simpFn_701_, lean_object* v_e_702_, lean_object* v_i_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_nat_dec_eq(v_i_703_, v___x_714_);
if (v___x_715_ == 0)
{
if (lean_obj_tag(v_e_702_) == 5)
{
lean_object* v_fn_716_; lean_object* v_arg_717_; lean_object* v___x_718_; lean_object* v_i_719_; lean_object* v___x_720_; 
v_fn_716_ = lean_ctor_get(v_e_702_, 0);
lean_inc_ref_n(v_fn_716_, 2);
v_arg_717_ = lean_ctor_get(v_e_702_, 1);
lean_inc_ref(v_arg_717_);
v___x_718_ = lean_unsigned_to_nat(1u);
v_i_719_ = lean_nat_sub(v_i_703_, v___x_718_);
v___x_720_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_701_, v_fn_716_, v_i_719_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_i_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
if (lean_obj_tag(v_a_721_) == 0)
{
lean_dec_ref_known(v_a_721_, 0);
lean_dec_ref(v_arg_717_);
lean_dec_ref_known(v_e_702_, 2);
lean_dec_ref(v_fn_716_);
return v___x_720_;
}
else
{
lean_object* v_e_x27_722_; lean_object* v_proof_723_; uint8_t v_done_724_; uint8_t v_contextDependent_725_; lean_object* v___x_726_; 
lean_dec_ref_known(v___x_720_, 1);
v_e_x27_722_ = lean_ctor_get(v_a_721_, 0);
lean_inc_ref(v_e_x27_722_);
v_proof_723_ = lean_ctor_get(v_a_721_, 1);
lean_inc_ref(v_proof_723_);
v_done_724_ = lean_ctor_get_uint8(v_a_721_, sizeof(void*)*2);
v_contextDependent_725_ = lean_ctor_get_uint8(v_a_721_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_721_, 2);
v___x_726_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_702_, v_fn_716_, v_arg_717_, v_e_x27_722_, v_proof_723_, v_done_724_, v_contextDependent_725_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_726_;
}
}
else
{
lean_dec_ref(v_arg_717_);
lean_dec_ref_known(v_e_702_, 2);
lean_dec_ref(v_fn_716_);
return v___x_720_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v_e_702_);
lean_dec_ref(v_simpFn_701_);
v___x_727_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
v___x_728_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_727_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_728_;
}
}
else
{
lean_object* v___x_729_; 
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_a_705_);
lean_inc(v_a_704_);
v___x_729_ = lean_apply_11(v_simpFn_701_, v_e_702_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, lean_box(0));
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* v_simpFn_730_, lean_object* v_e_731_, lean_object* v_i_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_730_, v_e_731_, v_i_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec(v_i_732_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* v_e_744_, lean_object* v_numArgs_745_, lean_object* v_simpFn_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_746_, v_e_744_, v_numArgs_745_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* v_e_758_, lean_object* v_numArgs_759_, lean_object* v_simpFn_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_758_, v_numArgs_759_, v_simpFn_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec(v_numArgs_759_);
return v_res_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_Expr_isForall(v_type_775_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_whnfD(v_type_775_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; uint8_t v___x_786_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_786_ = l_Lean_Expr_isForall(v_a_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v___x_787_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1);
v___x_788_ = l_Lean_MessageData_ofExpr(v_a_785_);
v___x_789_ = l_Lean_indentD(v___x_788_);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_787_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_790_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Sym_shareCommonInc(v_a_785_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_800_;
}
}
else
{
return v___x_784_;
}
}
else
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_type_775_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_810_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_933__overap_821_; lean_object* v___x_822_; 
v___x_820_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_933__overap_821_ = lean_panic_fn_borrowed(v___x_820_, v_msg_812_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
v___x_822_ = lean_apply_7(v___x_933__overap_821_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, lean_box(0));
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_834_ = lean_unsigned_to_nat(47u);
v___x_835_ = lean_unsigned_to_nat(207u);
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_838_ = l_mkPanicMessageWithDecl(v___x_837_, v___x_836_, v___x_835_, v___x_834_, v___x_833_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_839_, lean_object* v_n_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_zero_848_; uint8_t v_isZero_849_; 
v_zero_848_ = lean_unsigned_to_nat(0u);
v_isZero_849_ = lean_nat_dec_eq(v_n_840_, v_zero_848_);
if (v_isZero_849_ == 1)
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Meta_Sym_inferType(v_e_839_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_850_;
}
else
{
lean_object* v_one_851_; lean_object* v_n_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_one_851_ = lean_unsigned_to_nat(1u);
v_n_852_ = lean_nat_sub(v_n_840_, v_one_851_);
v___x_853_ = l_Lean_Expr_appFn_x21(v_e_839_);
lean_dec_ref(v_e_839_);
v___x_854_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_853_, v_n_852_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_n_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_855_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_867_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_867_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_867_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_867_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
if (lean_obj_tag(v_a_857_) == 7)
{
lean_object* v_body_861_; lean_object* v___x_863_; 
v_body_861_ = lean_ctor_get(v_a_857_, 2);
lean_inc_ref(v_body_861_);
lean_dec_ref_known(v_a_857_, 3);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v_body_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_body_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_del_object(v___x_859_);
lean_dec(v_a_857_);
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_866_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_865_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_866_;
}
}
}
else
{
return v___x_856_;
}
}
else
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_868_, lean_object* v_n_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_868_, v_n_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_n_869_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_878_, lean_object* v_a_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___y_888_; lean_object* v___x_891_; uint8_t v_debug_892_; 
v___x_891_ = lean_st_ref_get(v___y_881_);
v_debug_892_ = lean_ctor_get_uint8(v___x_891_, sizeof(void*)*11);
lean_dec(v___x_891_);
if (v_debug_892_ == 0)
{
v___y_888_ = v___y_881_;
goto v___jp_887_;
}
else
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_894_; 
lean_dec_ref_known(v___x_893_, 1);
v___x_894_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_dec_ref_known(v___x_894_, 1);
v___y_888_ = v___y_881_;
goto v___jp_887_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_a_879_);
lean_dec_ref(v_f_878_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
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
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_a_879_);
lean_dec_ref(v_f_878_);
v_a_903_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_893_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
v___jp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = l_Lean_Expr_app___override(v_f_878_, v_a_879_);
v___x_890_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_889_, v___y_888_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_911_, lean_object* v_a_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_911_, v_a_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_921_, lean_object* v_a_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_921_, v_a_922_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_934_, lean_object* v_a_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_934_, v_a_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
return v_res_946_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_27995__overap_960_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
v___x_27995__overap_960_ = lean_panic_fn_borrowed(v___x_959_, v_msg_948_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
v___x_961_ = lean_apply_10(v___x_27995__overap_960_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, lean_box(0));
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
return v_res_973_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_box(0);
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_979_ = l_Lean_Expr_const___override(v___x_978_, v___x_977_);
return v___x_979_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_982_ = lean_unsigned_to_nat(52u);
v___x_983_ = lean_unsigned_to_nat(269u);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_986_ = l_mkPanicMessageWithDecl(v___x_985_, v___x_984_, v___x_983_, v___x_982_, v___x_981_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_988_ = lean_unsigned_to_nat(52u);
v___x_989_ = lean_unsigned_to_nat(261u);
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_992_ = l_mkPanicMessageWithDecl(v___x_991_, v___x_990_, v___x_989_, v___x_988_, v___x_987_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_993_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_994_ = lean_unsigned_to_nat(52u);
v___x_995_ = lean_unsigned_to_nat(276u);
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_998_ = l_mkPanicMessageWithDecl(v___x_997_, v___x_996_, v___x_995_, v___x_994_, v___x_993_);
return v___x_998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1000_ = lean_unsigned_to_nat(26u);
v___x_1001_ = lean_unsigned_to_nat(254u);
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1004_ = l_mkPanicMessageWithDecl(v___x_1003_, v___x_1002_, v___x_1001_, v___x_1000_, v___x_999_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1010_, lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_nat_dec_eq(v_i_1010_, v___x_1022_);
if (v___x_1023_ == 0)
{
if (lean_obj_tag(v_e_1011_) == 5)
{
lean_object* v_fn_1024_; lean_object* v_arg_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_fn_1024_ = lean_ctor_get(v_e_1011_, 0);
lean_inc_ref_n(v_fn_1024_, 2);
v_arg_1025_ = lean_ctor_get(v_e_1011_, 1);
lean_inc_ref(v_arg_1025_);
lean_dec_ref_known(v_e_1011_, 2);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_sub(v_i_1010_, v___x_1026_);
v___x_1028_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1027_, v_fn_1024_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1287_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v_fst_1030_ = lean_ctor_get(v_a_1029_, 0);
v_snd_1031_ = lean_ctor_get(v_a_1029_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1033_ = v_a_1029_;
v_isShared_1034_ = v_isSharedCheck_1287_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_inc(v_fst_1030_);
lean_dec(v_a_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1287_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; 
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_a_1014_);
lean_inc_ref(v_a_1013_);
lean_inc(v_a_1012_);
lean_inc_ref(v_arg_1025_);
v___x_1035_ = lean_sym_simp(v_arg_1025_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1278_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1278_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1278_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
uint8_t v___y_1041_; uint8_t v___x_1050_; 
v___x_1050_ = 1;
if (lean_obj_tag(v_fst_1030_) == 0)
{
lean_dec(v_snd_1031_);
if (lean_obj_tag(v_a_1036_) == 0)
{
uint8_t v_contextDependent_1051_; 
lean_dec(v___x_1027_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_contextDependent_1051_ = lean_ctor_get_uint8(v_fst_1030_, 1);
lean_dec_ref_known(v_fst_1030_, 0);
if (v_contextDependent_1051_ == 0)
{
uint8_t v_contextDependent_1052_; 
v_contextDependent_1052_ = lean_ctor_get_uint8(v_a_1036_, 1);
lean_dec_ref_known(v_a_1036_, 0);
v___y_1041_ = v_contextDependent_1052_;
goto v___jp_1040_;
}
else
{
lean_dec_ref_known(v_a_1036_, 0);
v___y_1041_ = v___x_1050_;
goto v___jp_1040_;
}
}
else
{
uint8_t v_contextDependent_1053_; lean_object* v_e_x27_1054_; lean_object* v_proof_1055_; uint8_t v_contextDependent_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1133_; 
lean_del_object(v___x_1038_);
lean_del_object(v___x_1033_);
v_contextDependent_1053_ = lean_ctor_get_uint8(v_fst_1030_, 1);
lean_dec_ref_known(v_fst_1030_, 0);
v_e_x27_1054_ = lean_ctor_get(v_a_1036_, 0);
v_proof_1055_ = lean_ctor_get(v_a_1036_, 1);
v_contextDependent_1056_ = lean_ctor_get_uint8(v_a_1036_, sizeof(void*)*2 + 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_a_1036_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1058_ = v_a_1036_;
v_isShared_1059_ = v_isSharedCheck_1133_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_proof_1055_);
lean_inc(v_e_x27_1054_);
lean_dec(v_a_1036_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1133_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; 
lean_inc_ref(v_fn_1024_);
v___x_1060_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1024_, v___x_1027_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v___x_1027_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1062_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_1061_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
if (lean_obj_tag(v_a_1063_) == 7)
{
lean_object* v_binderType_1064_; lean_object* v_body_1065_; lean_object* v___x_1066_; 
v_binderType_1064_ = lean_ctor_get(v_a_1063_, 1);
lean_inc_ref(v_binderType_1064_);
v_body_1065_ = lean_ctor_get(v_a_1063_, 2);
lean_inc_ref(v_body_1065_);
lean_dec_ref_known(v_a_1063_, 3);
lean_inc_ref(v_e_x27_1054_);
lean_inc_ref(v_fn_1024_);
v___x_1066_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1024_, v_e_x27_1054_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
lean_inc_ref(v_binderType_1064_);
v___x_1068_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1064_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
lean_inc_ref(v_body_1065_);
v___x_1070_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1065_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1090_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1090_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1090_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___y_1082_; 
v___x_1075_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_a_1071_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_a_1069_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_mkConst(v___x_1075_, v___x_1078_);
lean_inc_ref(v_body_1065_);
v___x_1080_ = l_Lean_mkApp6(v___x_1079_, v_binderType_1064_, v_body_1065_, v_arg_1025_, v_e_x27_1054_, v_fn_1024_, v_proof_1055_);
if (v_contextDependent_1053_ == 0)
{
v___y_1082_ = v_contextDependent_1056_;
goto v___jp_1081_;
}
else
{
v___y_1082_ = v___x_1050_;
goto v___jp_1081_;
}
v___jp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1080_);
lean_ctor_set(v___x_1058_, 0, v_a_1067_);
v___x_1084_ = v___x_1058_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1067_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1080_);
v___x_1084_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*2, v___x_1023_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*2 + 1, v___y_1082_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_body_1065_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1085_);
v___x_1087_ = v___x_1073_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1069_);
lean_dec(v_a_1067_);
lean_dec_ref(v_body_1065_);
lean_dec_ref(v_binderType_1064_);
lean_del_object(v___x_1058_);
lean_dec_ref(v_proof_1055_);
lean_dec_ref(v_e_x27_1054_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1091_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1070_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1070_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_1067_);
lean_dec_ref(v_body_1065_);
lean_dec_ref(v_binderType_1064_);
lean_del_object(v___x_1058_);
lean_dec_ref(v_proof_1055_);
lean_dec_ref(v_e_x27_1054_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1099_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1068_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1068_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_body_1065_);
lean_dec_ref(v_binderType_1064_);
lean_del_object(v___x_1058_);
lean_dec_ref(v_proof_1055_);
lean_dec_ref(v_e_x27_1054_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1107_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1066_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1066_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
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
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_a_1063_);
lean_del_object(v___x_1058_);
lean_dec_ref(v_proof_1055_);
lean_dec_ref(v_e_x27_1054_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v___x_1115_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1116_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1115_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1116_;
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1058_);
lean_dec_ref(v_proof_1055_);
lean_dec_ref(v_e_x27_1054_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1117_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1062_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1062_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_del_object(v___x_1058_);
lean_dec_ref(v_proof_1055_);
lean_dec_ref(v_e_x27_1054_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1125_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1060_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1060_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1038_);
lean_del_object(v___x_1033_);
lean_dec(v___x_1027_);
if (lean_obj_tag(v_a_1036_) == 0)
{
lean_object* v_e_x27_1134_; lean_object* v_proof_1135_; uint8_t v_contextDependent_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1204_; 
v_e_x27_1134_ = lean_ctor_get(v_fst_1030_, 0);
v_proof_1135_ = lean_ctor_get(v_fst_1030_, 1);
v_contextDependent_1136_ = lean_ctor_get_uint8(v_fst_1030_, sizeof(void*)*2 + 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_fst_1030_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1138_ = v_fst_1030_;
v_isShared_1139_ = v_isSharedCheck_1204_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_proof_1135_);
lean_inc(v_e_x27_1134_);
lean_dec(v_fst_1030_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1204_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v_contextDependent_1140_; lean_object* v___x_1141_; 
v_contextDependent_1140_ = lean_ctor_get_uint8(v_a_1036_, 1);
lean_dec_ref_known(v_a_1036_, 0);
v___x_1141_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1031_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
if (lean_obj_tag(v_a_1142_) == 7)
{
lean_object* v_binderType_1143_; lean_object* v_body_1144_; lean_object* v___x_1145_; 
v_binderType_1143_ = lean_ctor_get(v_a_1142_, 1);
lean_inc_ref(v_binderType_1143_);
v_body_1144_ = lean_ctor_get(v_a_1142_, 2);
lean_inc_ref(v_body_1144_);
lean_dec_ref_known(v_a_1142_, 3);
lean_inc_ref(v_arg_1025_);
lean_inc_ref(v_e_x27_1134_);
v___x_1145_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1134_, v_arg_1025_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
lean_inc_ref(v_binderType_1143_);
v___x_1147_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1143_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
lean_inc_ref(v_body_1144_);
v___x_1149_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1144_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1169_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1169_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1169_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___y_1161_; 
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1150_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_a_1148_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_mkConst(v___x_1154_, v___x_1157_);
lean_inc_ref(v_body_1144_);
v___x_1159_ = l_Lean_mkApp6(v___x_1158_, v_binderType_1143_, v_body_1144_, v_fn_1024_, v_e_x27_1134_, v_proof_1135_, v_arg_1025_);
if (v_contextDependent_1136_ == 0)
{
v___y_1161_ = v_contextDependent_1140_;
goto v___jp_1160_;
}
else
{
v___y_1161_ = v___x_1050_;
goto v___jp_1160_;
}
v___jp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1159_);
lean_ctor_set(v___x_1138_, 0, v_a_1146_);
v___x_1163_ = v___x_1138_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1146_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1159_);
v___x_1163_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2, v___x_1023_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2 + 1, v___y_1161_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v_body_1144_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1164_);
v___x_1166_ = v___x_1152_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
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
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_a_1148_);
lean_dec(v_a_1146_);
lean_dec_ref(v_body_1144_);
lean_dec_ref(v_binderType_1143_);
lean_del_object(v___x_1138_);
lean_dec_ref(v_proof_1135_);
lean_dec_ref(v_e_x27_1134_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1170_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1149_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1149_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_a_1146_);
lean_dec_ref(v_body_1144_);
lean_dec_ref(v_binderType_1143_);
lean_del_object(v___x_1138_);
lean_dec_ref(v_proof_1135_);
lean_dec_ref(v_e_x27_1134_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1178_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1147_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1147_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_body_1144_);
lean_dec_ref(v_binderType_1143_);
lean_del_object(v___x_1138_);
lean_dec_ref(v_proof_1135_);
lean_dec_ref(v_e_x27_1134_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1186_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1145_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1145_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_a_1142_);
lean_del_object(v___x_1138_);
lean_dec_ref(v_proof_1135_);
lean_dec_ref(v_e_x27_1134_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v___x_1194_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1195_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1194_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1195_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1138_);
lean_dec_ref(v_proof_1135_);
lean_dec_ref(v_e_x27_1134_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1196_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1141_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1141_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1205_; lean_object* v_proof_1206_; uint8_t v_contextDependent_1207_; lean_object* v_e_x27_1208_; lean_object* v_proof_1209_; uint8_t v_contextDependent_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1277_; 
v_e_x27_1205_ = lean_ctor_get(v_fst_1030_, 0);
lean_inc_ref(v_e_x27_1205_);
v_proof_1206_ = lean_ctor_get(v_fst_1030_, 1);
lean_inc_ref(v_proof_1206_);
v_contextDependent_1207_ = lean_ctor_get_uint8(v_fst_1030_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1030_, 2);
v_e_x27_1208_ = lean_ctor_get(v_a_1036_, 0);
v_proof_1209_ = lean_ctor_get(v_a_1036_, 1);
v_contextDependent_1210_ = lean_ctor_get_uint8(v_a_1036_, sizeof(void*)*2 + 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_a_1036_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1212_ = v_a_1036_;
v_isShared_1213_ = v_isSharedCheck_1277_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_proof_1209_);
lean_inc(v_e_x27_1208_);
lean_dec(v_a_1036_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1277_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; 
v___x_1214_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1031_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
if (lean_obj_tag(v_a_1215_) == 7)
{
lean_object* v_binderType_1216_; lean_object* v_body_1217_; lean_object* v___x_1218_; 
v_binderType_1216_ = lean_ctor_get(v_a_1215_, 1);
lean_inc_ref(v_binderType_1216_);
v_body_1217_ = lean_ctor_get(v_a_1215_, 2);
lean_inc_ref(v_body_1217_);
lean_dec_ref_known(v_a_1215_, 3);
lean_inc_ref(v_e_x27_1208_);
lean_inc_ref(v_e_x27_1205_);
v___x_1218_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1205_, v_e_x27_1208_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
lean_inc_ref(v_binderType_1216_);
v___x_1220_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1216_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
lean_inc_ref(v_body_1217_);
v___x_1222_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1217_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1242_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1242_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1242_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___y_1234_; 
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1223_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_a_1221_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = l_Lean_mkConst(v___x_1227_, v___x_1230_);
lean_inc_ref(v_body_1217_);
v___x_1232_ = l_Lean_mkApp8(v___x_1231_, v_binderType_1216_, v_body_1217_, v_fn_1024_, v_e_x27_1205_, v_arg_1025_, v_e_x27_1208_, v_proof_1206_, v_proof_1209_);
if (v_contextDependent_1207_ == 0)
{
v___y_1234_ = v_contextDependent_1210_;
goto v___jp_1233_;
}
else
{
v___y_1234_ = v___x_1050_;
goto v___jp_1233_;
}
v___jp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1232_);
lean_ctor_set(v___x_1212_, 0, v_a_1219_);
v___x_1236_ = v___x_1212_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1219_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1232_);
v___x_1236_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*2, v___x_1023_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*2 + 1, v___y_1234_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_body_1217_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1237_);
v___x_1239_ = v___x_1225_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_a_1221_);
lean_dec(v_a_1219_);
lean_dec_ref(v_body_1217_);
lean_dec_ref(v_binderType_1216_);
lean_del_object(v___x_1212_);
lean_dec_ref(v_proof_1209_);
lean_dec_ref(v_e_x27_1208_);
lean_dec_ref(v_proof_1206_);
lean_dec_ref(v_e_x27_1205_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1243_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1222_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1222_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_body_1217_);
lean_dec_ref(v_binderType_1216_);
lean_del_object(v___x_1212_);
lean_dec_ref(v_proof_1209_);
lean_dec_ref(v_e_x27_1208_);
lean_dec_ref(v_proof_1206_);
lean_dec_ref(v_e_x27_1205_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1251_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1220_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1220_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_body_1217_);
lean_dec_ref(v_binderType_1216_);
lean_del_object(v___x_1212_);
lean_dec_ref(v_proof_1209_);
lean_dec_ref(v_e_x27_1208_);
lean_dec_ref(v_proof_1206_);
lean_dec_ref(v_e_x27_1205_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1259_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1218_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1218_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec(v_a_1215_);
lean_del_object(v___x_1212_);
lean_dec_ref(v_proof_1209_);
lean_dec_ref(v_e_x27_1208_);
lean_dec_ref(v_proof_1206_);
lean_dec_ref(v_e_x27_1205_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v___x_1267_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1268_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1267_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1268_;
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1212_);
lean_dec_ref(v_proof_1209_);
lean_dec_ref(v_e_x27_1208_);
lean_dec_ref(v_proof_1206_);
lean_dec_ref(v_e_x27_1205_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1269_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1214_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1214_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1042_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1041_);
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1043_);
lean_ctor_set(v___x_1033_, 0, v___x_1042_);
v___x_1045_ = v___x_1033_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1045_);
v___x_1047_ = v___x_1038_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1033_);
lean_dec(v_snd_1031_);
lean_dec(v_fst_1030_);
lean_dec(v___x_1027_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
v_a_1279_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1035_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1035_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
else
{
lean_dec(v___x_1027_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v_fn_1024_);
return v___x_1028_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v_e_1011_);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1289_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1288_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec_ref(v_e_1011_);
v___x_1290_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1292_, lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1292_, v_e_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec(v_i_1292_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1305_, lean_object* v_e_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1305_, v_e_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_fst_1322_; lean_object* v___x_1324_; 
v_fst_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_fst_1322_);
lean_dec(v_a_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v_fst_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_fst_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1317_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1317_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1335_, lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1335_, v_e_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec(v_n_1335_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1348_, lean_object* v_prefixSize_1349_, lean_object* v_suffixSize_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_numArgs_1361_; uint8_t v___x_1362_; 
v_numArgs_1361_ = l_Lean_Expr_getAppNumArgs(v_e_1348_);
v___x_1362_ = lean_nat_dec_le(v_numArgs_1361_, v_prefixSize_1349_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_nat_add(v_prefixSize_1349_, v_suffixSize_1350_);
v___x_1364_ = lean_nat_dec_lt(v___x_1363_, v_numArgs_1361_);
lean_dec(v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v_suffixSize_1350_);
v___x_1365_ = lean_nat_sub(v_numArgs_1361_, v_prefixSize_1349_);
lean_dec(v_numArgs_1361_);
v___x_1366_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1365_, v_e_1348_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v___x_1365_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1367_ = lean_nat_sub(v_numArgs_1361_, v_prefixSize_1349_);
lean_dec(v_numArgs_1361_);
v___x_1368_ = lean_nat_sub(v___x_1367_, v_suffixSize_1350_);
lean_dec(v___x_1367_);
v___x_1369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1369_, 0, v_suffixSize_1350_);
v___x_1370_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1369_, v_e_1348_, v___x_1368_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v___x_1368_);
return v___x_1370_;
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v_numArgs_1361_);
lean_dec(v_suffixSize_1350_);
lean_dec_ref(v_e_1348_);
v___x_1371_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1373_, lean_object* v_prefixSize_1374_, lean_object* v_suffixSize_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1373_, v_prefixSize_1374_, v_suffixSize_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec(v_prefixSize_1374_);
return v_res_1386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1388_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1389_ = lean_unsigned_to_nat(13u);
v___x_1390_ = lean_unsigned_to_nat(312u);
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1392_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1393_ = l_mkPanicMessageWithDecl(v___x_1392_, v___x_1391_, v___x_1390_, v___x_1389_, v___x_1388_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1394_, lean_object* v_i_1395_, lean_object* v_e_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_nat_dec_eq(v_i_1395_, v___x_1407_);
if (v___x_1408_ == 0)
{
if (lean_obj_tag(v_e_1396_) == 5)
{
lean_object* v_fn_1409_; lean_object* v_arg_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_fn_1409_ = lean_ctor_get(v_e_1396_, 0);
lean_inc_ref_n(v_fn_1409_, 2);
v_arg_1410_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_arg_1410_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_sub(v_i_1395_, v___x_1411_);
v___x_1413_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1394_, v___x_1412_, v_fn_1409_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1433_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1433_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1433_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_array_fget_borrowed(v_rewritable_1394_, v___x_1412_);
lean_dec(v___x_1412_);
v___x_1419_ = lean_unbox(v___x_1418_);
if (v___x_1419_ == 0)
{
if (lean_obj_tag(v_a_1414_) == 0)
{
uint8_t v_contextDependent_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
lean_dec_ref(v_arg_1410_);
lean_dec_ref_known(v_e_1396_, 2);
lean_dec_ref(v_fn_1409_);
v_contextDependent_1420_ = lean_ctor_get_uint8(v_a_1414_, 1);
lean_dec_ref_known(v_a_1414_, 0);
v___x_1421_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1420_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1421_);
v___x_1423_ = v___x_1416_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
lean_object* v_e_x27_1425_; lean_object* v_proof_1426_; uint8_t v_contextDependent_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; 
lean_del_object(v___x_1416_);
v_e_x27_1425_ = lean_ctor_get(v_a_1414_, 0);
lean_inc_ref(v_e_x27_1425_);
v_proof_1426_ = lean_ctor_get(v_a_1414_, 1);
lean_inc_ref(v_proof_1426_);
v_contextDependent_1427_ = lean_ctor_get_uint8(v_a_1414_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1414_, 2);
v___x_1428_ = lean_unbox(v___x_1418_);
v___x_1429_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1396_, v_fn_1409_, v_arg_1410_, v_e_x27_1425_, v_proof_1426_, v___x_1428_, v_contextDependent_1427_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1429_;
}
}
else
{
lean_object* v___x_1430_; 
lean_del_object(v___x_1416_);
lean_inc(v_a_1405_);
lean_inc_ref(v_a_1404_);
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
lean_inc(v_a_1401_);
lean_inc_ref(v_a_1400_);
lean_inc(v_a_1399_);
lean_inc_ref(v_a_1398_);
lean_inc(v_a_1397_);
lean_inc_ref(v_arg_1410_);
v___x_1430_ = lean_sym_simp(v_arg_1410_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1396_, v_fn_1409_, v_arg_1410_, v_a_1414_, v_a_1431_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1432_;
}
else
{
lean_dec(v_a_1414_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_fn_1409_);
lean_dec_ref_known(v_e_1396_, 2);
return v___x_1430_;
}
}
}
}
else
{
lean_dec(v___x_1412_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_fn_1409_);
lean_dec_ref_known(v_e_1396_, 2);
return v___x_1413_;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_e_1396_);
v___x_1434_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1435_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1434_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1435_;
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_e_1396_);
v___x_1436_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1438_, lean_object* v_i_1439_, lean_object* v_e_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1438_, v_i_1439_, v_e_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec(v_i_1439_);
lean_dec_ref(v_rewritable_1438_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1452_, lean_object* v_i_1453_, lean_object* v_e_1454_, lean_object* v_h_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1452_, v_i_1453_, v_e_1454_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1467_, lean_object* v_i_1468_, lean_object* v_e_1469_, lean_object* v_h_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1467_, v_i_1468_, v_e_1469_, v_h_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec(v_i_1468_);
lean_dec_ref(v_rewritable_1467_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1482_, lean_object* v___x_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1482_, v___x_1483_, v_x_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1496_, lean_object* v___x_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1496_, v___x_1497_, v_x_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec(v___x_1497_);
lean_dec_ref(v_rewritable_1496_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1510_, lean_object* v_rewritable_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_numArgs_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v_numArgs_1522_ = l_Lean_Expr_getAppNumArgs(v_e_1510_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_nat_dec_eq(v_numArgs_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = lean_array_get_size(v_rewritable_1511_);
v___x_1526_ = lean_nat_dec_lt(v___x_1525_, v_numArgs_1522_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
v___x_1527_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1511_, v_numArgs_1522_, v_e_1510_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_numArgs_1522_);
lean_dec_ref(v_rewritable_1511_);
return v___x_1527_;
}
else
{
lean_object* v___f_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___f_1528_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1528_, 0, v_rewritable_1511_);
lean_closure_set(v___f_1528_, 1, v___x_1525_);
v___x_1529_ = lean_nat_sub(v_numArgs_1522_, v___x_1525_);
lean_dec(v_numArgs_1522_);
v___x_1530_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1528_, v_e_1510_, v___x_1529_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v___x_1529_);
return v___x_1530_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_numArgs_1522_);
lean_dec_ref(v_rewritable_1511_);
lean_dec_ref(v_e_1510_);
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1533_, lean_object* v_rewritable_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1533_, v_rewritable_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1546_, lean_object* v_numEqs_1547_, lean_object* v_result_1548_){
_start:
{
if (lean_obj_tag(v_result_1548_) == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
lean_dec(v_numEqs_1547_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_array_get_size(v_argResults_1546_);
v___x_1551_ = lean_nat_dec_lt(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_dec_ref_known(v_result_1548_, 0);
return v_argResults_1546_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_array_push(v_argResults_1546_, v_result_1548_);
return v___x_1552_;
}
}
else
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = lean_array_get_size(v_argResults_1546_);
v___x_1554_ = lean_nat_dec_lt(v___x_1553_, v_numEqs_1547_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_numEqs_1547_);
v___x_1555_ = lean_array_push(v_argResults_1546_, v_result_1548_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref(v_argResults_1546_);
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1557_ = lean_mk_array(v_numEqs_1547_, v___x_1556_);
v___x_1558_ = lean_array_push(v___x_1557_, v_result_1548_);
return v___x_1558_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1560_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1561_ = lean_unsigned_to_nat(13u);
v___x_1562_ = lean_unsigned_to_nat(433u);
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1565_ = l_mkPanicMessageWithDecl(v___x_1564_, v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1566_, lean_object* v_mkNonRflResult_1567_, lean_object* v_e_1568_, lean_object* v_i_1569_, lean_object* v_numEqs_1570_, lean_object* v_argResults_1571_, uint8_t v_anyCD_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
if (lean_obj_tag(v_e_1568_) == 5)
{
lean_object* v_fn_1583_; lean_object* v_arg_1584_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_fn_1583_ = lean_ctor_get(v_e_1568_, 0);
lean_inc_ref(v_fn_1583_);
v_arg_1584_ = lean_ctor_get(v_e_1568_, 1);
lean_inc_ref(v_arg_1584_);
lean_dec_ref_known(v_e_1568_, 2);
v___x_1598_ = 0;
v___x_1599_ = lean_box(v___x_1598_);
v___x_1600_ = lean_array_get(v___x_1599_, v_argKinds_1566_, v_i_1569_);
lean_dec(v___x_1599_);
v___x_1601_ = lean_unbox(v___x_1600_);
lean_dec(v___x_1600_);
switch(v___x_1601_)
{
case 5:
{
lean_dec_ref(v_arg_1584_);
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
v___y_1593_ = v_a_1580_;
v___y_1594_ = v_a_1581_;
goto v___jp_1585_;
}
case 0:
{
lean_dec_ref(v_arg_1584_);
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
v___y_1593_ = v_a_1580_;
v___y_1594_ = v_a_1581_;
goto v___jp_1585_;
}
case 3:
{
lean_dec_ref(v_arg_1584_);
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
v___y_1593_ = v_a_1580_;
v___y_1594_ = v_a_1581_;
goto v___jp_1585_;
}
case 2:
{
lean_object* v___x_1602_; 
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc_ref(v_a_1574_);
lean_inc(v_a_1573_);
v___x_1602_ = lean_sym_simp(v_arg_1584_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_n(v_a_1603_, 2);
lean_dec_ref_known(v___x_1602_, 1);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_sub(v_i_1569_, v___x_1604_);
lean_dec(v_i_1569_);
v___x_1606_ = lean_nat_add(v_numEqs_1570_, v___x_1604_);
v___x_1607_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1571_, v_numEqs_1570_, v_a_1603_);
if (v_anyCD_1572_ == 0)
{
if (lean_obj_tag(v_a_1603_) == 0)
{
uint8_t v_contextDependent_1608_; 
v_contextDependent_1608_ = lean_ctor_get_uint8(v_a_1603_, 1);
lean_dec_ref_known(v_a_1603_, 0);
v_e_1568_ = v_fn_1583_;
v_i_1569_ = v___x_1605_;
v_numEqs_1570_ = v___x_1606_;
v_argResults_1571_ = v___x_1607_;
v_anyCD_1572_ = v_contextDependent_1608_;
goto _start;
}
else
{
uint8_t v_contextDependent_1610_; 
v_contextDependent_1610_ = lean_ctor_get_uint8(v_a_1603_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1603_, 2);
v_e_1568_ = v_fn_1583_;
v_i_1569_ = v___x_1605_;
v_numEqs_1570_ = v___x_1606_;
v_argResults_1571_ = v___x_1607_;
v_anyCD_1572_ = v_contextDependent_1610_;
goto _start;
}
}
else
{
lean_dec(v_a_1603_);
v_e_1568_ = v_fn_1583_;
v_i_1569_ = v___x_1605_;
v_numEqs_1570_ = v___x_1606_;
v_argResults_1571_ = v___x_1607_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_1583_);
lean_dec_ref(v_argResults_1571_);
lean_dec(v_numEqs_1570_);
lean_dec(v_i_1569_);
lean_dec_ref(v_mkNonRflResult_1567_);
return v___x_1602_;
}
}
default: 
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_fn_1583_);
lean_dec_ref(v_argResults_1571_);
lean_dec(v_numEqs_1570_);
lean_dec(v_i_1569_);
lean_dec_ref(v_mkNonRflResult_1567_);
v___x_1613_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1614_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1613_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1614_;
}
}
v___jp_1585_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_nat_sub(v_i_1569_, v___x_1595_);
lean_dec(v_i_1569_);
v_e_1568_ = v_fn_1583_;
v_i_1569_ = v___x_1596_;
v_a_1573_ = v___y_1586_;
v_a_1574_ = v___y_1587_;
v_a_1575_ = v___y_1588_;
v_a_1576_ = v___y_1589_;
v_a_1577_ = v___y_1590_;
v_a_1578_ = v___y_1591_;
v_a_1579_ = v___y_1592_;
v_a_1580_ = v___y_1593_;
v_a_1581_ = v___y_1594_;
goto _start;
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
lean_dec(v_numEqs_1570_);
lean_dec(v_i_1569_);
lean_dec_ref(v_e_1568_);
v___x_1615_ = lean_array_get_size(v_argResults_1571_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_nat_dec_eq(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = l_Array_reverse___redArg(v_argResults_1571_);
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc_ref(v_a_1574_);
lean_inc(v_a_1573_);
v___x_1619_ = lean_apply_11(v_mkNonRflResult_1567_, v___x_1618_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, lean_box(0));
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
if (v_anyCD_1572_ == 0)
{
lean_dec(v_a_1620_);
return v___x_1619_;
}
else
{
if (lean_obj_tag(v_a_1620_) == 0)
{
uint8_t v_contextDependent_1624_; 
v_contextDependent_1624_ = lean_ctor_get_uint8(v_a_1620_, 1);
if (v_contextDependent_1624_ == 0)
{
lean_dec_ref_known(v___x_1619_, 1);
goto v___jp_1621_;
}
else
{
lean_dec_ref_known(v_a_1620_, 0);
return v___x_1619_;
}
}
else
{
uint8_t v_contextDependent_1625_; 
v_contextDependent_1625_ = lean_ctor_get_uint8(v_a_1620_, sizeof(void*)*2 + 1);
if (v_contextDependent_1625_ == 0)
{
lean_dec_ref_known(v___x_1619_, 1);
goto v___jp_1621_;
}
else
{
lean_dec_ref_known(v_a_1620_, 2);
return v___x_1619_;
}
}
}
v___jp_1621_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1620_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
}
else
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v_argResults_1571_);
lean_dec_ref(v_mkNonRflResult_1567_);
v___x_1626_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_1572_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object** _args){
lean_object* v_argKinds_1628_ = _args[0];
lean_object* v_mkNonRflResult_1629_ = _args[1];
lean_object* v_e_1630_ = _args[2];
lean_object* v_i_1631_ = _args[3];
lean_object* v_numEqs_1632_ = _args[4];
lean_object* v_argResults_1633_ = _args[5];
lean_object* v_anyCD_1634_ = _args[6];
lean_object* v_a_1635_ = _args[7];
lean_object* v_a_1636_ = _args[8];
lean_object* v_a_1637_ = _args[9];
lean_object* v_a_1638_ = _args[10];
lean_object* v_a_1639_ = _args[11];
lean_object* v_a_1640_ = _args[12];
lean_object* v_a_1641_ = _args[13];
lean_object* v_a_1642_ = _args[14];
lean_object* v_a_1643_ = _args[15];
lean_object* v_a_1644_ = _args[16];
_start:
{
uint8_t v_anyCD_boxed_1645_; lean_object* v_res_1646_; 
v_anyCD_boxed_1645_ = lean_unbox(v_anyCD_1634_);
v_res_1646_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1628_, v_mkNonRflResult_1629_, v_e_1630_, v_i_1631_, v_numEqs_1632_, v_argResults_1633_, v_anyCD_boxed_1645_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_argKinds_1628_);
return v_res_1646_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_17246__overap_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
v___x_17246__overap_1660_ = lean_panic_fn_borrowed(v___x_1659_, v_msg_1648_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1649_);
v___x_1661_ = lean_apply_10(v___x_17246__overap_1660_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, lean_box(0));
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(uint8_t v___x_1674_, lean_object* v_as_1675_, size_t v_i_1676_, size_t v_stop_1677_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_eq(v_i_1676_, v_stop_1677_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = lean_array_uget_borrowed(v_as_1675_, v_i_1676_);
v___x_1684_ = lean_unbox(v___x_1683_);
if (v___x_1684_ == 3)
{
if (v___x_1674_ == 0)
{
goto v___jp_1678_;
}
else
{
return v___x_1674_;
}
}
else
{
goto v___jp_1678_;
}
}
else
{
uint8_t v___x_1685_; 
v___x_1685_ = 0;
return v___x_1685_;
}
v___jp_1678_:
{
size_t v___x_1679_; size_t v___x_1680_; 
v___x_1679_ = ((size_t)1ULL);
v___x_1680_ = lean_usize_add(v_i_1676_, v___x_1679_);
v_i_1676_ = v___x_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object* v___x_1686_, lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_stop_1689_){
_start:
{
uint8_t v___x_19065__boxed_1690_; size_t v_i_boxed_1691_; size_t v_stop_boxed_1692_; uint8_t v_res_1693_; lean_object* v_r_1694_; 
v___x_19065__boxed_1690_ = lean_unbox(v___x_1686_);
v_i_boxed_1691_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_stop_boxed_1692_ = lean_unbox_usize(v_stop_1689_);
lean_dec(v_stop_1689_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_19065__boxed_1690_, v_as_1687_, v_i_boxed_1691_, v_stop_boxed_1692_);
lean_dec_ref(v_as_1687_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object* v_as_1695_, size_t v_i_1696_, size_t v_stop_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_eq(v_i_1696_, v_stop_1697_);
if (v___x_1698_ == 0)
{
uint8_t v___x_1699_; uint8_t v___y_1701_; lean_object* v___x_1705_; 
v___x_1699_ = 1;
v___x_1705_ = lean_array_uget_borrowed(v_as_1695_, v_i_1696_);
if (lean_obj_tag(v___x_1705_) == 0)
{
uint8_t v_contextDependent_1706_; 
v_contextDependent_1706_ = lean_ctor_get_uint8(v___x_1705_, 1);
v___y_1701_ = v_contextDependent_1706_;
goto v___jp_1700_;
}
else
{
uint8_t v_contextDependent_1707_; 
v_contextDependent_1707_ = lean_ctor_get_uint8(v___x_1705_, sizeof(void*)*2 + 1);
v___y_1701_ = v_contextDependent_1707_;
goto v___jp_1700_;
}
v___jp_1700_:
{
if (v___y_1701_ == 0)
{
size_t v___x_1702_; size_t v___x_1703_; 
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_add(v_i_1696_, v___x_1702_);
v_i_1696_ = v___x_1703_;
goto _start;
}
else
{
return v___x_1699_;
}
}
}
else
{
uint8_t v___x_1708_; 
v___x_1708_ = 0;
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v_as_1709_, lean_object* v_i_1710_, lean_object* v_stop_1711_){
_start:
{
size_t v_i_boxed_1712_; size_t v_stop_boxed_1713_; uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_i_boxed_1712_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_stop_boxed_1713_ = lean_unbox_usize(v_stop_1711_);
lean_dec(v_stop_1711_);
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1709_, v_i_boxed_1712_, v_stop_boxed_1713_);
lean_dec_ref(v_as_1709_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1717_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1718_ = lean_unsigned_to_nat(13u);
v___x_1719_ = lean_unsigned_to_nat(405u);
v___x_1720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1722_ = l_mkPanicMessageWithDecl(v___x_1721_, v___x_1720_, v___x_1719_, v___x_1718_, v___x_1717_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1723_, lean_object* v_as_1724_, size_t v_sz_1725_, size_t v_i_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_a_1739_; uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1726_, v_sz_1725_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1727_);
return v___x_1744_;
}
else
{
lean_object* v_snd_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1940_; 
v_snd_1745_ = lean_ctor_get(v_b_1727_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_b_1727_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_b_1727_, 0);
lean_dec(v_unused_1941_);
v___x_1747_ = v_b_1727_;
v_isShared_1748_ = v_isSharedCheck_1940_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snd_1745_);
lean_dec(v_b_1727_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1940_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_snd_1749_; lean_object* v_snd_1750_; lean_object* v_snd_1751_; lean_object* v_snd_1752_; lean_object* v_fst_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1938_; 
v_snd_1749_ = lean_ctor_get(v_snd_1745_, 1);
lean_inc(v_snd_1749_);
v_snd_1750_ = lean_ctor_get(v_snd_1749_, 1);
lean_inc(v_snd_1750_);
v_snd_1751_ = lean_ctor_get(v_snd_1750_, 1);
lean_inc(v_snd_1751_);
v_snd_1752_ = lean_ctor_get(v_snd_1751_, 1);
lean_inc(v_snd_1752_);
v_fst_1753_ = lean_ctor_get(v_snd_1745_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_snd_1745_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_snd_1745_, 1);
lean_dec(v_unused_1939_);
v___x_1755_ = v_snd_1745_;
v_isShared_1756_ = v_isSharedCheck_1938_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_fst_1753_);
lean_dec(v_snd_1745_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1938_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_fst_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1936_; 
v_fst_1757_ = lean_ctor_get(v_snd_1749_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_snd_1749_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_snd_1749_, 1);
lean_dec(v_unused_1937_);
v___x_1759_ = v_snd_1749_;
v_isShared_1760_ = v_isSharedCheck_1936_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_fst_1757_);
lean_dec(v_snd_1749_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1936_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_fst_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1934_; 
v_fst_1761_ = lean_ctor_get(v_snd_1750_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_snd_1750_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_snd_1750_, 1);
lean_dec(v_unused_1935_);
v___x_1763_ = v_snd_1750_;
v_isShared_1764_ = v_isSharedCheck_1934_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_fst_1761_);
lean_dec(v_snd_1750_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1934_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_fst_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1932_; 
v_fst_1765_ = lean_ctor_get(v_snd_1751_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_snd_1751_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_snd_1751_, 1);
lean_dec(v_unused_1933_);
v___x_1767_ = v_snd_1751_;
v_isShared_1768_ = v_isSharedCheck_1932_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_fst_1765_);
lean_dec(v_snd_1751_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1932_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_array_1769_; lean_object* v_start_1770_; lean_object* v_stop_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_array_1769_ = lean_ctor_get(v_snd_1752_, 0);
v_start_1770_ = lean_ctor_get(v_snd_1752_, 1);
v_stop_1771_ = lean_ctor_get(v_snd_1752_, 2);
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_nat_dec_lt(v_start_1770_, v_stop_1771_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1775_; 
if (v_isShared_1768_ == 0)
{
v___x_1775_ = v___x_1767_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_fst_1765_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_snd_1752_);
v___x_1775_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v___x_1775_);
v___x_1777_ = v___x_1763_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_fst_1761_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1777_);
v___x_1779_ = v___x_1759_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_fst_1757_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___x_1779_);
v___x_1781_ = v___x_1755_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_fst_1753_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1781_);
lean_ctor_set(v___x_1747_, 0, v___x_1772_);
v___x_1783_ = v___x_1747_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
}
}
}
}
else
{
lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1928_; 
lean_inc(v_stop_1771_);
lean_inc(v_start_1770_);
lean_inc_ref(v_array_1769_);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_snd_1752_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; 
v_unused_1929_ = lean_ctor_get(v_snd_1752_, 2);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_snd_1752_, 1);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_snd_1752_, 0);
lean_dec(v_unused_1931_);
v___x_1791_ = v_snd_1752_;
v_isShared_1792_ = v_isSharedCheck_1928_;
goto v_resetjp_1790_;
}
else
{
lean_dec(v_snd_1752_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1928_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v_a_1793_ = lean_array_uget_borrowed(v_as_1724_, v_i_1726_);
v___x_1794_ = lean_array_fget(v_array_1769_, v_start_1770_);
v___x_1795_ = lean_unsigned_to_nat(1u);
v___x_1796_ = lean_nat_add(v_start_1770_, v___x_1795_);
lean_dec(v_start_1770_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1796_);
v___x_1798_ = v___x_1791_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_array_1769_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_stop_1771_);
v___x_1798_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_proof_1802_; lean_object* v_subst_1803_; uint8_t v___x_1829_; 
lean_inc(v_a_1793_);
v___x_1799_ = l_Lean_Expr_app___override(v_fst_1753_, v_a_1793_);
v___x_1800_ = l_Lean_Expr_bindingBody_x21(v_fst_1757_);
lean_dec(v_fst_1757_);
v___x_1829_ = lean_unbox(v___x_1794_);
lean_dec(v___x_1794_);
switch(v___x_1829_)
{
case 0:
{
lean_del_object(v___x_1767_);
lean_del_object(v___x_1763_);
lean_del_object(v___x_1759_);
lean_del_object(v___x_1755_);
lean_del_object(v___x_1747_);
goto v___jp_1822_;
}
case 3:
{
lean_del_object(v___x_1767_);
lean_del_object(v___x_1763_);
lean_del_object(v___x_1759_);
lean_del_object(v___x_1755_);
lean_del_object(v___x_1747_);
goto v___jp_1822_;
}
case 5:
{
lean_object* v___x_1830_; lean_object* v_instNew_1832_; lean_object* v___x_1841_; 
lean_del_object(v___x_1767_);
lean_del_object(v___x_1763_);
lean_del_object(v___x_1759_);
lean_del_object(v___x_1755_);
lean_del_object(v___x_1747_);
lean_inc_n(v_a_1793_, 2);
v___x_1830_ = lean_array_push(v_fst_1765_, v_a_1793_);
v___x_1841_ = l_Lean_Meta_Sym_inferType(v_a_1793_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_Expr_bindingDomain_x21(v___x_1800_);
v___x_1844_ = lean_expr_instantiate_rev(v___x_1843_, v___x_1830_);
lean_dec_ref(v___x_1843_);
lean_inc_ref(v___x_1844_);
v___x_1845_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_1842_, v___x_1844_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; uint8_t v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = lean_unbox(v_a_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Meta_trySynthInstance(v___x_1844_, v___x_1772_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1866_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1866_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1866_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
if (lean_obj_tag(v_a_1849_) == 1)
{
lean_object* v_a_1853_; 
lean_del_object(v___x_1851_);
lean_dec(v_a_1846_);
v_a_1853_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v_a_1849_, 1);
v_instNew_1832_ = v_a_1853_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1854_; uint8_t v___x_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_dec(v_a_1849_);
v___x_1854_ = lean_alloc_ctor(0, 0, 2);
v___x_1855_ = lean_unbox(v_a_1846_);
lean_ctor_set_uint8(v___x_1854_, 0, v___x_1855_);
v___x_1856_ = lean_unbox(v_a_1846_);
lean_dec(v_a_1846_);
lean_ctor_set_uint8(v___x_1854_, 1, v___x_1856_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1830_);
lean_ctor_set(v___x_1858_, 1, v___x_1798_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_fst_1761_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1800_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1799_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1857_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1862_);
v___x_1864_ = v___x_1851_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1846_);
lean_dec_ref(v___x_1830_);
lean_dec_ref(v___x_1800_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec(v_fst_1761_);
v_a_1867_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1848_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1848_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_dec(v_a_1846_);
lean_dec_ref(v___x_1844_);
lean_inc(v_a_1793_);
v_instNew_1832_ = v_a_1793_;
goto v___jp_1831_;
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v___x_1844_);
lean_dec_ref(v___x_1830_);
lean_dec_ref(v___x_1800_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec(v_fst_1761_);
v_a_1875_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1845_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1845_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v___x_1800_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec(v_fst_1761_);
v_a_1883_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1841_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1841_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_inc_ref(v_instNew_1832_);
v___x_1833_ = l_Lean_Expr_app___override(v___x_1799_, v_instNew_1832_);
v___x_1834_ = lean_array_push(v___x_1830_, v_instNew_1832_);
v___x_1835_ = l_Lean_Expr_bindingBody_x21(v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1798_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_fst_1761_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1833_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1772_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v_a_1739_ = v___x_1840_;
goto v___jp_1738_;
}
}
case 2:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1793_);
v___x_1892_ = lean_array_push(v_fst_1765_, v_a_1793_);
v___x_1893_ = lean_array_get_borrowed(v___x_1891_, v_argResults_1723_, v_fst_1761_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; 
lean_inc(v_a_1793_);
v___x_1894_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1793_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_n(v_a_1895_, 2);
lean_dec_ref_known(v___x_1894_, 1);
lean_inc_n(v_a_1793_, 2);
v___x_1896_ = l_Lean_mkAppB(v___x_1799_, v_a_1793_, v_a_1895_);
v___x_1897_ = lean_array_push(v___x_1892_, v_a_1793_);
v___x_1898_ = lean_array_push(v___x_1897_, v_a_1895_);
v_proof_1802_ = v___x_1896_;
v_subst_1803_ = v___x_1898_;
goto v___jp_1801_;
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v___x_1892_);
lean_dec_ref(v___x_1800_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_del_object(v___x_1767_);
lean_del_object(v___x_1763_);
lean_dec(v_fst_1761_);
lean_del_object(v___x_1759_);
lean_del_object(v___x_1755_);
lean_del_object(v___x_1747_);
v_a_1899_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1894_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1894_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_e_x27_1907_; lean_object* v_proof_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_e_x27_1907_ = lean_ctor_get(v___x_1893_, 0);
v_proof_1908_ = lean_ctor_get(v___x_1893_, 1);
lean_inc_ref_n(v_proof_1908_, 2);
lean_inc_ref_n(v_e_x27_1907_, 2);
v___x_1909_ = l_Lean_mkAppB(v___x_1799_, v_e_x27_1907_, v_proof_1908_);
v___x_1910_ = lean_array_push(v___x_1892_, v_e_x27_1907_);
v___x_1911_ = lean_array_push(v___x_1910_, v_proof_1908_);
v_proof_1802_ = v___x_1909_;
v_subst_1803_ = v___x_1911_;
goto v___jp_1801_;
}
}
default: 
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_del_object(v___x_1767_);
lean_del_object(v___x_1763_);
lean_del_object(v___x_1759_);
lean_del_object(v___x_1755_);
lean_del_object(v___x_1747_);
v___x_1912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
v___x_1913_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_1912_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec_ref_known(v___x_1913_, 1);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_fst_1765_);
lean_ctor_set(v___x_1914_, 1, v___x_1798_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_fst_1761_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1800_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1799_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1772_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v_a_1739_ = v___x_1918_;
goto v___jp_1738_;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___x_1800_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec(v_fst_1765_);
lean_dec(v_fst_1761_);
v_a_1919_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1913_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1913_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
v___jp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1804_ = l_Lean_Expr_bindingBody_x21(v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1805_ = l_Lean_Expr_bindingBody_x21(v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = lean_nat_add(v_fst_1761_, v___x_1795_);
lean_dec(v_fst_1761_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1798_);
lean_ctor_set(v___x_1767_, 0, v_subst_1803_);
v___x_1808_ = v___x_1767_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_subst_1803_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1798_);
v___x_1808_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v___x_1808_);
lean_ctor_set(v___x_1763_, 0, v___x_1806_);
v___x_1810_ = v___x_1763_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1810_);
lean_ctor_set(v___x_1759_, 0, v___x_1805_);
v___x_1812_ = v___x_1759_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___x_1812_);
lean_ctor_set(v___x_1755_, 0, v_proof_1802_);
v___x_1814_ = v___x_1755_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_proof_1802_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1814_);
lean_ctor_set(v___x_1747_, 0, v___x_1772_);
v___x_1816_ = v___x_1747_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
v_a_1739_ = v___x_1816_;
goto v___jp_1738_;
}
}
}
}
}
}
v___jp_1822_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc(v_a_1793_);
v___x_1823_ = lean_array_push(v_fst_1765_, v_a_1793_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1798_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_fst_1761_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1800_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1799_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1772_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v_a_1739_ = v___x_1828_;
goto v___jp_1738_;
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
v___jp_1738_:
{
size_t v___x_1740_; size_t v___x_1741_; 
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1726_, v___x_1740_);
v_i_1726_ = v___x_1741_;
v_b_1727_ = v_a_1739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_1942_, lean_object* v_as_1943_, lean_object* v_sz_1944_, lean_object* v_i_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
size_t v_sz_boxed_1957_; size_t v_i_boxed_1958_; lean_object* v_res_1959_; 
v_sz_boxed_1957_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1958_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1942_, v_as_1943_, v_sz_boxed_1957_, v_i_boxed_1958_, v_b_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v_as_1943_);
lean_dec_ref(v_argResults_1942_);
return v_res_1959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1961_ = lean_unsigned_to_nat(34u);
v___x_1962_ = lean_unsigned_to_nat(406u);
v___x_1963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1965_ = l_mkPanicMessageWithDecl(v___x_1964_, v___x_1963_, v___x_1962_, v___x_1961_, v___x_1960_);
return v___x_1965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1968_; lean_object* v_dummy_1969_; 
v___x_1968_ = lean_box(0);
v_dummy_1969_ = l_Lean_Expr_sort___override(v___x_1968_);
return v_dummy_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_1973_, lean_object* v_argKinds_1974_, lean_object* v_type_1975_, lean_object* v_proof_1976_, lean_object* v_argResults_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v_j_2000_; lean_object* v_subst_2001_; lean_object* v_dummy_2002_; lean_object* v_nargs_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v_args_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; size_t v_sz_2016_; size_t v___x_2017_; lean_object* v___x_2018_; 
v_j_2000_ = lean_unsigned_to_nat(0u);
v_subst_2001_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2002_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2003_ = l_Lean_Expr_getAppNumArgs(v_e_1973_);
lean_inc(v_nargs_2003_);
v___x_2004_ = lean_mk_array(v_nargs_2003_, v_dummy_2002_);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_sub(v_nargs_2003_, v___x_2005_);
lean_dec(v_nargs_2003_);
v_args_2007_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1973_, v___x_2004_, v___x_2006_);
v___x_2008_ = lean_array_get_size(v_argKinds_1974_);
lean_inc_ref(v_argKinds_1974_);
v___x_2009_ = l_Array_toSubarray___redArg(v_argKinds_1974_, v_j_2000_, v___x_2008_);
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_subst_2001_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_j_2000_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_type_1975_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_proof_1976_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2010_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v_sz_2016_ = lean_array_size(v_args_2007_);
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1977_, v_args_2007_, v_sz_2016_, v___x_2017_, v___x_2015_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec_ref(v_args_2007_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2089_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2089_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2089_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v_fst_2023_; 
v_fst_2023_ = lean_ctor_get(v_a_2019_, 0);
if (lean_obj_tag(v_fst_2023_) == 0)
{
lean_object* v_snd_2024_; lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___y_2028_; uint8_t v___y_2029_; lean_object* v_rhs_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v_fst_2057_; lean_object* v_snd_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_snd_2024_ = lean_ctor_get(v_a_2019_, 1);
lean_inc(v_snd_2024_);
lean_dec(v_a_2019_);
v_fst_2025_ = lean_ctor_get(v_snd_2024_, 0);
lean_inc(v_fst_2025_);
v_snd_2026_ = lean_ctor_get(v_snd_2024_, 1);
lean_inc(v_snd_2026_);
lean_dec(v_snd_2024_);
v_fst_2057_ = lean_ctor_get(v_snd_2026_, 0);
lean_inc(v_fst_2057_);
v_snd_2058_ = lean_ctor_get(v_snd_2026_, 1);
lean_inc(v_snd_2058_);
lean_dec(v_snd_2026_);
v___x_2059_ = l_Lean_Expr_cleanupAnnotations(v_fst_2057_);
v___x_2060_ = l_Lean_Expr_isApp(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec(v_snd_2058_);
lean_dec(v_fst_2025_);
lean_del_object(v___x_2021_);
lean_dec_ref(v_argKinds_1974_);
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
goto v___jp_1988_;
}
else
{
lean_object* v_arg_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_arg_2061_ = lean_ctor_get(v___x_2059_, 1);
lean_inc_ref(v_arg_2061_);
v___x_2062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2059_);
v___x_2063_ = l_Lean_Expr_isApp(v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec(v_snd_2058_);
lean_dec(v_fst_2025_);
lean_del_object(v___x_2021_);
lean_dec_ref(v_argKinds_1974_);
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2062_);
v___x_2065_ = l_Lean_Expr_isApp(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_arg_2061_);
lean_dec(v_snd_2058_);
lean_dec(v_fst_2025_);
lean_del_object(v___x_2021_);
lean_dec_ref(v_argKinds_1974_);
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2064_);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2068_ = l_Lean_Expr_isConstOf(v___x_2066_, v___x_2067_);
lean_dec_ref(v___x_2066_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v_arg_2061_);
lean_dec(v_snd_2058_);
lean_dec(v_fst_2025_);
lean_del_object(v___x_2021_);
lean_dec_ref(v_argKinds_1974_);
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
goto v___jp_1988_;
}
else
{
lean_object* v_snd_2069_; lean_object* v_fst_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_snd_2069_ = lean_ctor_get(v_snd_2058_, 1);
lean_inc(v_snd_2069_);
lean_dec(v_snd_2058_);
v_fst_2070_ = lean_ctor_get(v_snd_2069_, 0);
lean_inc(v_fst_2070_);
lean_dec(v_snd_2069_);
v___x_2071_ = lean_expr_instantiate_rev(v_arg_2061_, v_fst_2070_);
lean_dec(v_fst_2070_);
lean_dec_ref(v_arg_2061_);
v___x_2072_ = lean_nat_dec_lt(v_j_2000_, v___x_2008_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v_argKinds_1974_);
v_rhs_2036_ = v___x_2071_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
goto v___jp_2035_;
}
else
{
if (v___x_2072_ == 0)
{
lean_dec_ref(v_argKinds_1974_);
v_rhs_2036_ = v___x_2071_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
goto v___jp_2035_;
}
else
{
size_t v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_usize_of_nat(v___x_2008_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_2068_, v_argKinds_1974_, v___x_2017_, v___x_2073_);
lean_dec_ref(v_argKinds_1974_);
if (v___x_2074_ == 0)
{
v_rhs_2036_ = v___x_2071_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2071_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v_rhs_2036_ = v_a_2076_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
goto v___jp_2035_;
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_fst_2025_);
lean_del_object(v___x_2021_);
v_a_2077_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
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
v___jp_2027_:
{
uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2030_ = 0;
v___x_2031_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2031_, 0, v___y_2028_);
lean_ctor_set(v___x_2031_, 1, v_fst_2025_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*2, v___x_2030_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*2 + 1, v___y_2029_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2031_);
v___x_2033_ = v___x_2021_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
v___jp_2035_:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Meta_Sym_shareCommonInc(v_rhs_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = lean_array_get_size(v_argResults_1977_);
v___x_2046_ = lean_nat_dec_lt(v_j_2000_, v___x_2045_);
if (v___x_2046_ == 0)
{
v___y_2028_ = v_a_2044_;
v___y_2029_ = v___x_2046_;
goto v___jp_2027_;
}
else
{
if (v___x_2046_ == 0)
{
v___y_2028_ = v_a_2044_;
v___y_2029_ = v___x_2046_;
goto v___jp_2027_;
}
else
{
size_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_usize_of_nat(v___x_2045_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_1977_, v___x_2017_, v___x_2047_);
v___y_2028_ = v_a_2044_;
v___y_2029_ = v___x_2048_;
goto v___jp_2027_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_fst_2025_);
lean_del_object(v___x_2021_);
v_a_2049_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2043_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2043_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v_val_2085_; lean_object* v___x_2087_; 
lean_inc_ref(v_fst_2023_);
lean_dec(v_a_2019_);
lean_dec_ref(v_argKinds_1974_);
v_val_2085_ = lean_ctor_get(v_fst_2023_, 0);
lean_inc(v_val_2085_);
lean_dec_ref_known(v_fst_2023_, 1);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v_val_2085_);
v___x_2087_ = v___x_2021_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_argKinds_1974_);
v_a_2090_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2018_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2018_);
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
v___jp_1988_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_1999_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1998_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2098_, lean_object* v_argKinds_2099_, lean_object* v_type_2100_, lean_object* v_proof_2101_, lean_object* v_argResults_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2098_, v_argKinds_2099_, v_type_2100_, v_proof_2101_, v_argResults_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v_argResults_2102_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2114_, lean_object* v_x_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2126_, 0, v___x_2114_);
lean_ctor_set_uint8(v___x_2126_, 1, v___x_2114_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2128_, lean_object* v_x_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___x_19798__boxed_2140_; lean_object* v_res_2141_; 
v___x_19798__boxed_2140_ = lean_unbox(v___x_2128_);
v_res_2141_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_19798__boxed_2140_, v_x_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v_x_2129_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2144_, lean_object* v_argKinds_2145_, lean_object* v_mkNonRflResult_2146_, lean_object* v_x_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_sub(v___x_2144_, v___x_2158_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2162_ = 0;
v___x_2163_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2145_, v_mkNonRflResult_2146_, v_x_2147_, v___x_2159_, v___x_2160_, v___x_2161_, v___x_2162_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2164_, lean_object* v_argKinds_2165_, lean_object* v_mkNonRflResult_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2164_, v_argKinds_2165_, v_mkNonRflResult_2166_, v_x_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v_argKinds_2165_);
lean_dec(v___x_2164_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2179_, lean_object* v_thm_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_type_2191_; lean_object* v_proof_2192_; lean_object* v_argKinds_2193_; lean_object* v_mkNonRflResult_2194_; lean_object* v_numArgs_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_type_2191_ = lean_ctor_get(v_thm_2180_, 0);
lean_inc_ref(v_type_2191_);
v_proof_2192_ = lean_ctor_get(v_thm_2180_, 1);
lean_inc_ref(v_proof_2192_);
v_argKinds_2193_ = lean_ctor_get(v_thm_2180_, 2);
lean_inc_ref_n(v_argKinds_2193_, 2);
lean_dec_ref(v_thm_2180_);
lean_inc_ref(v_e_2179_);
v_mkNonRflResult_2194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2194_, 0, v_e_2179_);
lean_closure_set(v_mkNonRflResult_2194_, 1, v_argKinds_2193_);
lean_closure_set(v_mkNonRflResult_2194_, 2, v_type_2191_);
lean_closure_set(v_mkNonRflResult_2194_, 3, v_proof_2192_);
v_numArgs_2195_ = l_Lean_Expr_getAppNumArgs(v_e_2179_);
v___x_2196_ = lean_array_get_size(v_argKinds_2193_);
v___x_2197_ = lean_nat_dec_lt(v___x_2196_, v_numArgs_2195_);
if (v___x_2197_ == 0)
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_lt(v_numArgs_2195_, v___x_2196_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v_numArgs_2195_);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_sub(v___x_2196_, v___x_2199_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2203_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2193_, v_mkNonRflResult_2194_, v_e_2179_, v___x_2200_, v___x_2201_, v___x_2202_, v___x_2198_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec_ref(v_argKinds_2193_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_mkNonRflResult_2194_);
lean_dec_ref(v_argKinds_2193_);
v___x_2204_ = lean_box(v___x_2197_);
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2205_, 0, v___x_2204_);
v___x_2206_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2205_, v_e_2179_, v_numArgs_2195_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec(v_numArgs_2195_);
return v___x_2206_;
}
}
else
{
lean_object* v___f_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2207_, 0, v___x_2196_);
lean_closure_set(v___f_2207_, 1, v_argKinds_2193_);
lean_closure_set(v___f_2207_, 2, v_mkNonRflResult_2194_);
v___x_2208_ = lean_nat_sub(v_numArgs_2195_, v___x_2196_);
lean_dec(v_numArgs_2195_);
v___x_2209_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2207_, v_e_2179_, v___x_2208_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec(v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2210_, lean_object* v_thm_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2210_, v_thm_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_f_2234_; lean_object* v___x_2235_; 
v_f_2234_ = l_Lean_Expr_getAppFn(v_e_2223_);
v___x_2235_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2234_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2251_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2251_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2251_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
switch(lean_obj_tag(v_a_2236_))
{
case 0:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec_ref(v_e_2223_);
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
case 1:
{
lean_object* v_prefixSize_2244_; lean_object* v_suffixSize_2245_; lean_object* v___x_2246_; 
lean_del_object(v___x_2238_);
v_prefixSize_2244_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_prefixSize_2244_);
v_suffixSize_2245_ = lean_ctor_get(v_a_2236_, 1);
lean_inc(v_suffixSize_2245_);
lean_dec_ref_known(v_a_2236_, 2);
v___x_2246_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2223_, v_prefixSize_2244_, v_suffixSize_2245_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_prefixSize_2244_);
return v___x_2246_;
}
case 2:
{
lean_object* v_rewritable_2247_; lean_object* v___x_2248_; 
lean_del_object(v___x_2238_);
v_rewritable_2247_ = lean_ctor_get(v_a_2236_, 0);
lean_inc_ref(v_rewritable_2247_);
lean_dec_ref_known(v_a_2236_, 1);
v___x_2248_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2223_, v_rewritable_2247_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2248_;
}
default: 
{
lean_object* v_thm_2249_; lean_object* v___x_2250_; 
lean_del_object(v___x_2238_);
v_thm_2249_ = lean_ctor_get(v_a_2236_, 0);
lean_inc_ref(v_thm_2249_);
lean_dec_ref_known(v_a_2236_, 1);
v___x_2250_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2223_, v_thm_2249_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref(v_e_2223_);
v_a_2252_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2235_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2235_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
return v_res_2271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2274_ = lean_unsigned_to_nat(55u);
v___x_2275_ = lean_unsigned_to_nat(493u);
v___x_2276_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2277_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2278_ = l_mkPanicMessageWithDecl(v___x_2277_, v___x_2276_, v___x_2275_, v___x_2274_, v___x_2273_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2280_ = lean_unsigned_to_nat(11u);
v___x_2281_ = lean_unsigned_to_nat(501u);
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2284_ = l_mkPanicMessageWithDecl(v___x_2283_, v___x_2282_, v___x_2281_, v___x_2280_, v___x_2279_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2285_, lean_object* v_e_2286_, lean_object* v_i_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
uint8_t v_cd_2299_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_nat_dec_eq(v_i_2287_, v___x_2302_);
if (v___x_2303_ == 0)
{
if (lean_obj_tag(v_e_2286_) == 5)
{
lean_object* v_fn_2304_; lean_object* v_arg_2305_; lean_object* v___x_2306_; lean_object* v_i_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; 
v_fn_2304_ = lean_ctor_get(v_e_2286_, 0);
lean_inc_ref_n(v_fn_2304_, 2);
v_arg_2305_ = lean_ctor_get(v_e_2286_, 1);
lean_inc_ref(v_arg_2305_);
v___x_2306_ = lean_unsigned_to_nat(1u);
v_i_2307_ = lean_nat_sub(v_i_2287_, v___x_2306_);
v___x_2308_ = lean_nat_dec_lt(v_i_2307_, v_stop_2285_);
v___x_2309_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2285_, v_fn_2304_, v_i_2307_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_i_2307_);
if (lean_obj_tag(v___x_2309_) == 0)
{
if (v___x_2308_ == 0)
{
lean_object* v_a_2310_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
if (lean_obj_tag(v_a_2310_) == 0)
{
uint8_t v_contextDependent_2311_; 
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
v_contextDependent_2311_ = lean_ctor_get_uint8(v_a_2310_, 1);
lean_dec_ref_known(v_a_2310_, 0);
v_cd_2299_ = v_contextDependent_2311_;
goto v___jp_2298_;
}
else
{
lean_object* v_e_x27_2312_; lean_object* v_proof_2313_; uint8_t v_contextDependent_2314_; lean_object* v___x_2315_; 
v_e_x27_2312_ = lean_ctor_get(v_a_2310_, 0);
lean_inc_ref(v_e_x27_2312_);
v_proof_2313_ = lean_ctor_get(v_a_2310_, 1);
lean_inc_ref(v_proof_2313_);
v_contextDependent_2314_ = lean_ctor_get_uint8(v_a_2310_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2310_, 2);
v___x_2315_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2286_, v_fn_2304_, v_arg_2305_, v_e_x27_2312_, v_proof_2313_, v___x_2303_, v_contextDependent_2314_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2315_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2309_, 1);
lean_inc_ref(v_fn_2304_);
v___x_2317_ = l_Lean_Meta_Sym_inferType(v_fn_2304_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = l_Lean_Meta_whnfD(v_a_2318_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
if (lean_obj_tag(v_a_2320_) == 7)
{
lean_object* v_binderType_2321_; lean_object* v_body_2322_; uint8_t v___x_2323_; 
v_binderType_2321_ = lean_ctor_get(v_a_2320_, 1);
lean_inc_ref(v_binderType_2321_);
v_body_2322_ = lean_ctor_get(v_a_2320_, 2);
lean_inc_ref(v_body_2322_);
lean_dec_ref_known(v_a_2320_, 3);
v___x_2323_ = l_Lean_Expr_hasLooseBVars(v_body_2322_);
lean_dec_ref(v_body_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_isProp(v_binderType_2321_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_arg_2305_);
v___x_2327_ = lean_sym_simp(v_arg_2305_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2286_, v_fn_2304_, v_arg_2305_, v_a_2316_, v_a_2328_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2329_;
}
else
{
lean_dec(v_a_2316_);
lean_dec_ref(v_arg_2305_);
lean_dec_ref_known(v_e_2286_, 2);
lean_dec_ref(v_fn_2304_);
return v___x_2327_;
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2330_, 0, v___x_2303_);
lean_ctor_set_uint8(v___x_2330_, 1, v___x_2303_);
v___x_2331_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2286_, v_fn_2304_, v_arg_2305_, v_a_2316_, v___x_2330_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2331_;
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2316_);
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
v_a_2332_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2324_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2324_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_2321_);
if (lean_obj_tag(v_a_2316_) == 0)
{
uint8_t v_contextDependent_2340_; 
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
v_contextDependent_2340_ = lean_ctor_get_uint8(v_a_2316_, 1);
lean_dec_ref_known(v_a_2316_, 0);
v_cd_2299_ = v_contextDependent_2340_;
goto v___jp_2298_;
}
else
{
lean_object* v_e_x27_2341_; lean_object* v_proof_2342_; uint8_t v_contextDependent_2343_; lean_object* v___x_2344_; 
v_e_x27_2341_ = lean_ctor_get(v_a_2316_, 0);
lean_inc_ref(v_e_x27_2341_);
v_proof_2342_ = lean_ctor_get(v_a_2316_, 1);
lean_inc_ref(v_proof_2342_);
v_contextDependent_2343_ = lean_ctor_get_uint8(v_a_2316_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2316_, 2);
v___x_2344_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2286_, v_fn_2304_, v_arg_2305_, v_e_x27_2341_, v_proof_2342_, v___x_2303_, v_contextDependent_2343_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2344_;
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec(v_a_2320_);
lean_dec(v_a_2316_);
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
v___x_2345_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2346_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2345_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2346_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_a_2316_);
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
v_a_2347_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2319_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2319_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_a_2316_);
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
v_a_2355_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2317_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2317_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2305_);
lean_dec_ref(v_fn_2304_);
lean_dec_ref_known(v_e_2286_, 2);
return v___x_2309_;
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_e_2286_);
v___x_2363_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2364_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2363_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2364_;
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec_ref(v_e_2286_);
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
v___jp_2298_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2367_, lean_object* v_e_2368_, lean_object* v_i_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2367_, v_e_2368_, v_i_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec(v_i_2369_);
lean_dec(v_stop_2367_);
return v_res_2380_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2383_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2384_ = lean_unsigned_to_nat(2u);
v___x_2385_ = lean_unsigned_to_nat(476u);
v___x_2386_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2388_ = l_mkPanicMessageWithDecl(v___x_2387_, v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2389_, lean_object* v_start_2390_, lean_object* v_stop_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = lean_nat_dec_lt(v_start_2390_, v_stop_2391_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_dec_ref(v_e_2389_);
v___x_2403_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2404_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2403_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2404_;
}
else
{
lean_object* v_numArgs_2405_; uint8_t v___x_2406_; 
v_numArgs_2405_ = l_Lean_Expr_getAppNumArgs(v_e_2389_);
v___x_2406_ = lean_nat_dec_lt(v_numArgs_2405_, v_start_2390_);
if (v___x_2406_ == 0)
{
lean_object* v_numArgs_2407_; lean_object* v_stop_2408_; lean_object* v___x_2409_; 
v_numArgs_2407_ = lean_nat_sub(v_numArgs_2405_, v_start_2390_);
lean_dec(v_numArgs_2405_);
v_stop_2408_ = lean_nat_sub(v_stop_2391_, v_start_2390_);
v___x_2409_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2408_, v_e_2389_, v_numArgs_2407_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_numArgs_2407_);
lean_dec(v_stop_2408_);
return v___x_2409_;
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v_numArgs_2405_);
lean_dec_ref(v_e_2389_);
v___x_2410_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2412_, lean_object* v_start_2413_, lean_object* v_stop_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2412_, v_start_2413_, v_stop_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec(v_stop_2414_);
lean_dec(v_start_2413_);
return v_res_2425_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
