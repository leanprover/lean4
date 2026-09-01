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
v_options_311_ = lean_ctor_get(v___y_303_, 1);
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
v_ref_328_ = lean_ctor_get(v___y_325_, 4);
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
v___x_366_ = l_Lean_Meta_Sym_inferType(v_f_353_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = l_Lean_Meta_whnfD(v_a_367_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
if (lean_obj_tag(v_a_369_) == 7)
{
lean_object* v_binderName_370_; lean_object* v_body_371_; lean_object* v___x_372_; 
v_binderName_370_ = lean_ctor_get(v_a_369_, 0);
lean_inc(v_binderName_370_);
v_body_371_ = lean_ctor_get(v_a_369_, 2);
lean_inc_ref(v_body_371_);
lean_dec_ref_known(v_a_369_, 3);
lean_inc_ref(v_a_354_);
v___x_372_ = l_Lean_Meta_Sym_inferType(v_a_354_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_n(v_a_373_, 2);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_373_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v___x_376_ = l_Lean_Meta_Sym_inferType(v_e_352_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v___x_378_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
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
lean_object* v___x_541_; lean_object* v___x_6782__overap_542_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_6782__overap_542_ = lean_panic_fn_borrowed(v___x_541_, v_msg_530_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc(v___y_537_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
v___x_543_ = lean_apply_10(v___x_6782__overap_542_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, lean_box(0));
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
v___x_561_ = lean_unsigned_to_nat(127u);
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
v___x_567_ = lean_unsigned_to_nat(139u);
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
switch(lean_obj_tag(v_e_572_))
{
case 10:
{
lean_object* v_expr_586_; 
v_expr_586_ = lean_ctor_get(v_e_572_, 1);
lean_inc_ref(v_expr_586_);
lean_dec_ref_known(v_e_572_, 2);
v_e_572_ = v_expr_586_;
goto _start;
}
case 5:
{
lean_object* v_fn_588_; lean_object* v_arg_589_; lean_object* v___x_590_; lean_object* v_i_591_; lean_object* v___x_592_; 
v_fn_588_ = lean_ctor_get(v_e_572_, 0);
lean_inc_ref_n(v_fn_588_, 2);
v_arg_589_ = lean_ctor_get(v_e_572_, 1);
lean_inc_ref(v_arg_589_);
v___x_590_ = lean_unsigned_to_nat(1u);
v_i_591_ = lean_nat_sub(v_i_573_, v___x_590_);
v___x_592_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_571_, v_fn_588_, v_i_591_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_i_591_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
lean_inc_ref(v_fn_588_);
v___x_594_ = l_Lean_Meta_Sym_inferType(v_fn_588_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = l_Lean_Meta_whnfD(v_a_595_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_631_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_631_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_631_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_631_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
if (lean_obj_tag(v_a_597_) == 7)
{
lean_object* v_binderType_601_; lean_object* v_body_602_; uint8_t v___x_603_; 
v_binderType_601_ = lean_ctor_get(v_a_597_, 1);
lean_inc_ref(v_binderType_601_);
v_body_602_ = lean_ctor_get(v_a_597_, 2);
lean_inc_ref(v_body_602_);
lean_dec_ref_known(v_a_597_, 3);
v___x_603_ = l_Lean_Expr_hasLooseBVars(v_body_602_);
lean_dec_ref(v_body_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_del_object(v___x_599_);
v___x_604_ = l_Lean_Meta_isProp(v_binderType_601_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; uint8_t v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_inc(v_a_582_);
lean_inc_ref(v_a_581_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_arg_589_);
v___x_607_ = lean_sym_simp(v_arg_589_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_572_, v_fn_588_, v_arg_589_, v_a_593_, v_a_608_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_609_;
}
else
{
lean_dec(v_a_593_);
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
return v___x_607_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_610_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_610_, 1, v___x_585_);
v___x_611_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_572_, v_fn_588_, v_arg_589_, v_a_593_, v___x_610_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_611_;
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_593_);
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
v_a_612_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_604_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_604_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_601_);
if (lean_obj_tag(v_a_593_) == 0)
{
uint8_t v_contextDependent_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
v_contextDependent_620_ = lean_ctor_get_uint8(v_a_593_, 1);
lean_dec_ref_known(v_a_593_, 0);
v___x_621_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_620_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_621_);
v___x_623_ = v___x_599_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v_e_x27_625_; lean_object* v_proof_626_; uint8_t v_contextDependent_627_; lean_object* v___x_628_; 
lean_del_object(v___x_599_);
v_e_x27_625_ = lean_ctor_get(v_a_593_, 0);
lean_inc_ref(v_e_x27_625_);
v_proof_626_ = lean_ctor_get(v_a_593_, 1);
lean_inc_ref(v_proof_626_);
v_contextDependent_627_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_593_, 2);
v___x_628_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_572_, v_fn_588_, v_arg_589_, v_e_x27_625_, v_proof_626_, v___x_585_, v_contextDependent_627_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_628_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
v___x_629_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
v___x_630_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_629_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_630_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_a_593_);
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
v_a_632_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_596_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_596_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_593_);
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
v_a_640_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_594_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_594_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_dec_ref(v_arg_589_);
lean_dec_ref_known(v_e_572_, 2);
lean_dec_ref(v_fn_588_);
return v___x_592_;
}
}
default: 
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v_e_572_);
lean_dec_ref(v_simpFn_571_);
v___x_648_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
v___x_649_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_648_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_649_;
}
}
}
else
{
lean_object* v___x_650_; 
lean_inc(v_a_582_);
lean_inc_ref(v_a_581_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
v___x_650_ = lean_apply_11(v_simpFn_571_, v_e_572_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, lean_box(0));
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* v_simpFn_651_, lean_object* v_e_652_, lean_object* v_i_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_651_, v_e_652_, v_i_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec(v_i_653_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* v_e_665_, lean_object* v_numArgs_666_, lean_object* v_simpFn_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_667_, v_e_665_, v_numArgs_666_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* v_e_679_, lean_object* v_numArgs_680_, lean_object* v_simpFn_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_679_, v_numArgs_680_, v_simpFn_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec(v_numArgs_680_);
return v_res_692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_695_ = lean_unsigned_to_nat(13u);
v___x_696_ = lean_unsigned_to_nat(176u);
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* v_simpFn_700_, lean_object* v_e_701_, lean_object* v_i_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_nat_dec_eq(v_i_702_, v___x_713_);
if (v___x_714_ == 0)
{
if (lean_obj_tag(v_e_701_) == 5)
{
lean_object* v_fn_715_; lean_object* v_arg_716_; lean_object* v___x_717_; lean_object* v_i_718_; lean_object* v___x_719_; 
v_fn_715_ = lean_ctor_get(v_e_701_, 0);
lean_inc_ref_n(v_fn_715_, 2);
v_arg_716_ = lean_ctor_get(v_e_701_, 1);
lean_inc_ref(v_arg_716_);
v___x_717_ = lean_unsigned_to_nat(1u);
v_i_718_ = lean_nat_sub(v_i_702_, v___x_717_);
v___x_719_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_700_, v_fn_715_, v_i_718_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_i_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
if (lean_obj_tag(v_a_720_) == 0)
{
lean_dec_ref_known(v_a_720_, 0);
lean_dec_ref(v_arg_716_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_715_);
return v___x_719_;
}
else
{
lean_object* v_e_x27_721_; lean_object* v_proof_722_; uint8_t v_done_723_; uint8_t v_contextDependent_724_; lean_object* v___x_725_; 
lean_dec_ref_known(v___x_719_, 1);
v_e_x27_721_ = lean_ctor_get(v_a_720_, 0);
lean_inc_ref(v_e_x27_721_);
v_proof_722_ = lean_ctor_get(v_a_720_, 1);
lean_inc_ref(v_proof_722_);
v_done_723_ = lean_ctor_get_uint8(v_a_720_, sizeof(void*)*2);
v_contextDependent_724_ = lean_ctor_get_uint8(v_a_720_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_720_, 2);
v___x_725_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_701_, v_fn_715_, v_arg_716_, v_e_x27_721_, v_proof_722_, v_done_723_, v_contextDependent_724_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_725_;
}
}
else
{
lean_dec_ref(v_arg_716_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_715_);
return v___x_719_;
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_e_701_);
lean_dec_ref(v_simpFn_700_);
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
v___x_727_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_726_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_727_;
}
}
else
{
lean_object* v___x_728_; 
lean_inc(v_a_711_);
lean_inc_ref(v_a_710_);
lean_inc(v_a_709_);
lean_inc_ref(v_a_708_);
lean_inc(v_a_707_);
lean_inc_ref(v_a_706_);
lean_inc(v_a_705_);
lean_inc_ref(v_a_704_);
lean_inc(v_a_703_);
v___x_728_ = lean_apply_11(v_simpFn_700_, v_e_701_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, lean_box(0));
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* v_simpFn_729_, lean_object* v_e_730_, lean_object* v_i_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_729_, v_e_730_, v_i_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec(v_i_731_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* v_e_743_, lean_object* v_numArgs_744_, lean_object* v_simpFn_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_745_, v_e_743_, v_numArgs_744_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* v_e_757_, lean_object* v_numArgs_758_, lean_object* v_simpFn_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_757_, v_numArgs_758_, v_simpFn_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec(v_numArgs_758_);
return v_res_770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = l_Lean_Expr_isForall(v_type_774_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_whnfD(v_type_774_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; uint8_t v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = l_Lean_Expr_isForall(v_a_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v___x_786_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1);
v___x_787_ = l_Lean_MessageData_ofExpr(v_a_784_);
v___x_788_ = l_Lean_indentD(v___x_787_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_789_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Sym_shareCommonInc(v_a_784_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_799_;
}
}
else
{
return v___x_783_;
}
}
else
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_type_774_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
return v_res_809_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_933__overap_820_; lean_object* v___x_821_; 
v___x_819_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_933__overap_820_ = lean_panic_fn_borrowed(v___x_819_, v_msg_811_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
v___x_821_ = lean_apply_7(v___x_933__overap_820_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_833_ = lean_unsigned_to_nat(47u);
v___x_834_ = lean_unsigned_to_nat(207u);
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_837_ = l_mkPanicMessageWithDecl(v___x_836_, v___x_835_, v___x_834_, v___x_833_, v___x_832_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_838_, lean_object* v_n_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_zero_847_; uint8_t v_isZero_848_; 
v_zero_847_ = lean_unsigned_to_nat(0u);
v_isZero_848_ = lean_nat_dec_eq(v_n_839_, v_zero_847_);
if (v_isZero_848_ == 1)
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Meta_Sym_inferType(v_e_838_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_849_;
}
else
{
lean_object* v_one_850_; lean_object* v_n_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_one_850_ = lean_unsigned_to_nat(1u);
v_n_851_ = lean_nat_sub(v_n_839_, v_one_850_);
v___x_852_ = l_Lean_Expr_appFn_x21(v_e_838_);
lean_dec_ref(v_e_838_);
v___x_853_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_852_, v_n_851_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_n_851_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_854_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
if (lean_obj_tag(v_a_856_) == 7)
{
lean_object* v_body_860_; lean_object* v___x_862_; 
v_body_860_ = lean_ctor_get(v_a_856_, 2);
lean_inc_ref(v_body_860_);
lean_dec_ref_known(v_a_856_, 3);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v_body_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_body_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_del_object(v___x_858_);
lean_dec(v_a_856_);
v___x_864_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_865_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_864_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_865_;
}
}
}
else
{
return v___x_855_;
}
}
else
{
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_867_, lean_object* v_n_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_867_, v_n_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_n_868_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_877_, lean_object* v_a_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___y_887_; lean_object* v___x_890_; uint8_t v_debug_891_; 
v___x_890_ = lean_st_ref_get(v___y_880_);
v_debug_891_ = lean_ctor_get_uint8(v___x_890_, sizeof(void*)*11);
lean_dec(v___x_890_);
if (v_debug_891_ == 0)
{
v___y_887_ = v___y_880_;
goto v___jp_886_;
}
else
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; 
lean_dec_ref_known(v___x_892_, 1);
v___x_893_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_dec_ref_known(v___x_893_, 1);
v___y_887_ = v___y_880_;
goto v___jp_886_;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_a_878_);
lean_dec_ref(v_f_877_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_a_878_);
lean_dec_ref(v_f_877_);
v_a_902_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_892_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_892_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = l_Lean_Expr_app___override(v_f_877_, v_a_878_);
v___x_889_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_888_, v___y_887_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_910_, lean_object* v_a_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_910_, v_a_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_920_, lean_object* v_a_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_920_, v_a_921_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_933_, lean_object* v_a_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_933_, v_a_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
return v_res_945_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_27995__overap_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
v___x_27995__overap_959_ = lean_panic_fn_borrowed(v___x_958_, v_msg_947_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
v___x_960_ = lean_apply_10(v___x_27995__overap_959_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
return v_res_972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_box(0);
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_978_ = l_Lean_Expr_const___override(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_981_ = lean_unsigned_to_nat(52u);
v___x_982_ = lean_unsigned_to_nat(269u);
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_985_ = l_mkPanicMessageWithDecl(v___x_984_, v___x_983_, v___x_982_, v___x_981_, v___x_980_);
return v___x_985_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_987_ = lean_unsigned_to_nat(52u);
v___x_988_ = lean_unsigned_to_nat(261u);
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_991_ = l_mkPanicMessageWithDecl(v___x_990_, v___x_989_, v___x_988_, v___x_987_, v___x_986_);
return v___x_991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_993_ = lean_unsigned_to_nat(52u);
v___x_994_ = lean_unsigned_to_nat(276u);
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_997_ = l_mkPanicMessageWithDecl(v___x_996_, v___x_995_, v___x_994_, v___x_993_, v___x_992_);
return v___x_997_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_999_ = lean_unsigned_to_nat(26u);
v___x_1000_ = lean_unsigned_to_nat(254u);
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1003_ = l_mkPanicMessageWithDecl(v___x_1002_, v___x_1001_, v___x_1000_, v___x_999_, v___x_998_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1009_, lean_object* v_e_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_nat_dec_eq(v_i_1009_, v___x_1021_);
if (v___x_1022_ == 0)
{
if (lean_obj_tag(v_e_1010_) == 5)
{
lean_object* v_fn_1023_; lean_object* v_arg_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_fn_1023_ = lean_ctor_get(v_e_1010_, 0);
lean_inc_ref_n(v_fn_1023_, 2);
v_arg_1024_ = lean_ctor_get(v_e_1010_, 1);
lean_inc_ref(v_arg_1024_);
lean_dec_ref_known(v_e_1010_, 2);
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_sub(v_i_1009_, v___x_1025_);
v___x_1027_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1026_, v_fn_1023_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1286_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_fst_1029_ = lean_ctor_get(v_a_1028_, 0);
v_snd_1030_ = lean_ctor_get(v_a_1028_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1032_ = v_a_1028_;
v_isShared_1033_ = v_isSharedCheck_1286_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1030_);
lean_inc(v_fst_1029_);
lean_dec(v_a_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1286_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; 
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc_ref(v_a_1012_);
lean_inc(v_a_1011_);
lean_inc_ref(v_arg_1024_);
v___x_1034_ = lean_sym_simp(v_arg_1024_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1277_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1277_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1277_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___y_1040_; uint8_t v___x_1049_; 
v___x_1049_ = 1;
if (lean_obj_tag(v_fst_1029_) == 0)
{
lean_dec(v_snd_1030_);
if (lean_obj_tag(v_a_1035_) == 0)
{
uint8_t v_contextDependent_1050_; 
lean_dec(v___x_1026_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_contextDependent_1050_ = lean_ctor_get_uint8(v_fst_1029_, 1);
lean_dec_ref_known(v_fst_1029_, 0);
if (v_contextDependent_1050_ == 0)
{
uint8_t v_contextDependent_1051_; 
v_contextDependent_1051_ = lean_ctor_get_uint8(v_a_1035_, 1);
lean_dec_ref_known(v_a_1035_, 0);
v___y_1040_ = v_contextDependent_1051_;
goto v___jp_1039_;
}
else
{
lean_dec_ref_known(v_a_1035_, 0);
v___y_1040_ = v___x_1049_;
goto v___jp_1039_;
}
}
else
{
uint8_t v_contextDependent_1052_; lean_object* v_e_x27_1053_; lean_object* v_proof_1054_; uint8_t v_contextDependent_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1132_; 
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
v_contextDependent_1052_ = lean_ctor_get_uint8(v_fst_1029_, 1);
lean_dec_ref_known(v_fst_1029_, 0);
v_e_x27_1053_ = lean_ctor_get(v_a_1035_, 0);
v_proof_1054_ = lean_ctor_get(v_a_1035_, 1);
v_contextDependent_1055_ = lean_ctor_get_uint8(v_a_1035_, sizeof(void*)*2 + 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1057_ = v_a_1035_;
v_isShared_1058_ = v_isSharedCheck_1132_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_proof_1054_);
lean_inc(v_e_x27_1053_);
lean_dec(v_a_1035_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1132_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; 
lean_inc_ref(v_fn_1023_);
v___x_1059_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1023_, v___x_1026_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v___x_1026_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_1060_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
if (lean_obj_tag(v_a_1062_) == 7)
{
lean_object* v_binderType_1063_; lean_object* v_body_1064_; lean_object* v___x_1065_; 
v_binderType_1063_ = lean_ctor_get(v_a_1062_, 1);
lean_inc_ref(v_binderType_1063_);
v_body_1064_ = lean_ctor_get(v_a_1062_, 2);
lean_inc_ref(v_body_1064_);
lean_dec_ref_known(v_a_1062_, 3);
lean_inc_ref(v_e_x27_1053_);
lean_inc_ref(v_fn_1023_);
v___x_1065_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1023_, v_e_x27_1053_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
lean_inc_ref(v_binderType_1063_);
v___x_1067_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1063_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
lean_inc_ref(v_body_1064_);
v___x_1069_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1064_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1089_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1089_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1089_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___y_1081_; 
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1070_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_a_1068_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_mkConst(v___x_1074_, v___x_1077_);
lean_inc_ref(v_body_1064_);
v___x_1079_ = l_Lean_mkApp6(v___x_1078_, v_binderType_1063_, v_body_1064_, v_arg_1024_, v_e_x27_1053_, v_fn_1023_, v_proof_1054_);
if (v_contextDependent_1052_ == 0)
{
v___y_1081_ = v_contextDependent_1055_;
goto v___jp_1080_;
}
else
{
v___y_1081_ = v___x_1049_;
goto v___jp_1080_;
}
v___jp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1079_);
lean_ctor_set(v___x_1057_, 0, v_a_1066_);
v___x_1083_ = v___x_1057_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1066_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1079_);
v___x_1083_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*2, v___x_1022_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*2 + 1, v___y_1081_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_body_1064_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1084_);
v___x_1086_ = v___x_1072_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1068_);
lean_dec(v_a_1066_);
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_binderType_1063_);
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1090_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1069_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1069_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_a_1066_);
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_binderType_1063_);
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1098_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1067_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1067_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_binderType_1063_);
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1106_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1065_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1065_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_a_1062_);
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v___x_1114_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1115_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1114_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1115_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1116_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1061_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1061_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1124_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1059_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1059_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec(v___x_1026_);
if (lean_obj_tag(v_a_1035_) == 0)
{
lean_object* v_e_x27_1133_; lean_object* v_proof_1134_; uint8_t v_contextDependent_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1203_; 
v_e_x27_1133_ = lean_ctor_get(v_fst_1029_, 0);
v_proof_1134_ = lean_ctor_get(v_fst_1029_, 1);
v_contextDependent_1135_ = lean_ctor_get_uint8(v_fst_1029_, sizeof(void*)*2 + 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_fst_1029_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1137_ = v_fst_1029_;
v_isShared_1138_ = v_isSharedCheck_1203_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_proof_1134_);
lean_inc(v_e_x27_1133_);
lean_dec(v_fst_1029_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1203_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint8_t v_contextDependent_1139_; lean_object* v___x_1140_; 
v_contextDependent_1139_ = lean_ctor_get_uint8(v_a_1035_, 1);
lean_dec_ref_known(v_a_1035_, 0);
v___x_1140_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1030_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
if (lean_obj_tag(v_a_1141_) == 7)
{
lean_object* v_binderType_1142_; lean_object* v_body_1143_; lean_object* v___x_1144_; 
v_binderType_1142_ = lean_ctor_get(v_a_1141_, 1);
lean_inc_ref(v_binderType_1142_);
v_body_1143_ = lean_ctor_get(v_a_1141_, 2);
lean_inc_ref(v_body_1143_);
lean_dec_ref_known(v_a_1141_, 3);
lean_inc_ref(v_arg_1024_);
lean_inc_ref(v_e_x27_1133_);
v___x_1144_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1133_, v_arg_1024_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
lean_inc_ref(v_binderType_1142_);
v___x_1146_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1142_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
lean_inc_ref(v_body_1143_);
v___x_1148_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1143_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1168_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1168_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1168_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___y_1160_; 
v___x_1153_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1149_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1147_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_mkConst(v___x_1153_, v___x_1156_);
lean_inc_ref(v_body_1143_);
v___x_1158_ = l_Lean_mkApp6(v___x_1157_, v_binderType_1142_, v_body_1143_, v_fn_1023_, v_e_x27_1133_, v_proof_1134_, v_arg_1024_);
if (v_contextDependent_1135_ == 0)
{
v___y_1160_ = v_contextDependent_1139_;
goto v___jp_1159_;
}
else
{
v___y_1160_ = v___x_1049_;
goto v___jp_1159_;
}
v___jp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1158_);
lean_ctor_set(v___x_1137_, 0, v_a_1145_);
v___x_1162_ = v___x_1137_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1145_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1158_);
v___x_1162_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*2, v___x_1022_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*2 + 1, v___y_1160_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_body_1143_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1163_);
v___x_1165_ = v___x_1151_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_a_1147_);
lean_dec(v_a_1145_);
lean_dec_ref(v_body_1143_);
lean_dec_ref(v_binderType_1142_);
lean_del_object(v___x_1137_);
lean_dec_ref(v_proof_1134_);
lean_dec_ref(v_e_x27_1133_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1169_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1148_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1148_);
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
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1145_);
lean_dec_ref(v_body_1143_);
lean_dec_ref(v_binderType_1142_);
lean_del_object(v___x_1137_);
lean_dec_ref(v_proof_1134_);
lean_dec_ref(v_e_x27_1133_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1177_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1146_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1146_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_body_1143_);
lean_dec_ref(v_binderType_1142_);
lean_del_object(v___x_1137_);
lean_dec_ref(v_proof_1134_);
lean_dec_ref(v_e_x27_1133_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1185_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1144_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1144_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_a_1141_);
lean_del_object(v___x_1137_);
lean_dec_ref(v_proof_1134_);
lean_dec_ref(v_e_x27_1133_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v___x_1193_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1194_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1193_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1194_;
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_del_object(v___x_1137_);
lean_dec_ref(v_proof_1134_);
lean_dec_ref(v_e_x27_1133_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1195_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1140_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1140_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1204_; lean_object* v_proof_1205_; uint8_t v_contextDependent_1206_; lean_object* v_e_x27_1207_; lean_object* v_proof_1208_; uint8_t v_contextDependent_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1276_; 
v_e_x27_1204_ = lean_ctor_get(v_fst_1029_, 0);
lean_inc_ref(v_e_x27_1204_);
v_proof_1205_ = lean_ctor_get(v_fst_1029_, 1);
lean_inc_ref(v_proof_1205_);
v_contextDependent_1206_ = lean_ctor_get_uint8(v_fst_1029_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1029_, 2);
v_e_x27_1207_ = lean_ctor_get(v_a_1035_, 0);
v_proof_1208_ = lean_ctor_get(v_a_1035_, 1);
v_contextDependent_1209_ = lean_ctor_get_uint8(v_a_1035_, sizeof(void*)*2 + 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1211_ = v_a_1035_;
v_isShared_1212_ = v_isSharedCheck_1276_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_proof_1208_);
lean_inc(v_e_x27_1207_);
lean_dec(v_a_1035_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1276_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1030_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
if (lean_obj_tag(v_a_1214_) == 7)
{
lean_object* v_binderType_1215_; lean_object* v_body_1216_; lean_object* v___x_1217_; 
v_binderType_1215_ = lean_ctor_get(v_a_1214_, 1);
lean_inc_ref(v_binderType_1215_);
v_body_1216_ = lean_ctor_get(v_a_1214_, 2);
lean_inc_ref(v_body_1216_);
lean_dec_ref_known(v_a_1214_, 3);
lean_inc_ref(v_e_x27_1207_);
lean_inc_ref(v_e_x27_1204_);
v___x_1217_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1204_, v_e_x27_1207_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
lean_inc_ref(v_binderType_1215_);
v___x_1219_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1215_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
lean_inc_ref(v_body_1216_);
v___x_1221_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1216_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1241_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1241_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1241_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___y_1233_; 
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1222_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1220_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_mkConst(v___x_1226_, v___x_1229_);
lean_inc_ref(v_body_1216_);
v___x_1231_ = l_Lean_mkApp8(v___x_1230_, v_binderType_1215_, v_body_1216_, v_fn_1023_, v_e_x27_1204_, v_arg_1024_, v_e_x27_1207_, v_proof_1205_, v_proof_1208_);
if (v_contextDependent_1206_ == 0)
{
v___y_1233_ = v_contextDependent_1209_;
goto v___jp_1232_;
}
else
{
v___y_1233_ = v___x_1049_;
goto v___jp_1232_;
}
v___jp_1232_:
{
lean_object* v___x_1235_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1231_);
lean_ctor_set(v___x_1211_, 0, v_a_1218_);
v___x_1235_ = v___x_1211_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1218_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1231_);
v___x_1235_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*2, v___x_1022_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*2 + 1, v___y_1233_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_body_1216_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1236_);
v___x_1238_ = v___x_1224_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_a_1220_);
lean_dec(v_a_1218_);
lean_dec_ref(v_body_1216_);
lean_dec_ref(v_binderType_1215_);
lean_del_object(v___x_1211_);
lean_dec_ref(v_proof_1208_);
lean_dec_ref(v_e_x27_1207_);
lean_dec_ref(v_proof_1205_);
lean_dec_ref(v_e_x27_1204_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1242_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1221_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1221_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1218_);
lean_dec_ref(v_body_1216_);
lean_dec_ref(v_binderType_1215_);
lean_del_object(v___x_1211_);
lean_dec_ref(v_proof_1208_);
lean_dec_ref(v_e_x27_1207_);
lean_dec_ref(v_proof_1205_);
lean_dec_ref(v_e_x27_1204_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1250_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1219_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1219_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v_body_1216_);
lean_dec_ref(v_binderType_1215_);
lean_del_object(v___x_1211_);
lean_dec_ref(v_proof_1208_);
lean_dec_ref(v_e_x27_1207_);
lean_dec_ref(v_proof_1205_);
lean_dec_ref(v_e_x27_1204_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1258_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1217_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1217_);
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
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_a_1214_);
lean_del_object(v___x_1211_);
lean_dec_ref(v_proof_1208_);
lean_dec_ref(v_e_x27_1207_);
lean_dec_ref(v_proof_1205_);
lean_dec_ref(v_e_x27_1204_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v___x_1266_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1267_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1266_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1267_;
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_del_object(v___x_1211_);
lean_dec_ref(v_proof_1208_);
lean_dec_ref(v_e_x27_1207_);
lean_dec_ref(v_proof_1205_);
lean_dec_ref(v_e_x27_1204_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1268_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1213_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1213_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1041_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1042_);
lean_ctor_set(v___x_1032_, 0, v___x_1041_);
v___x_1044_ = v___x_1032_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1044_);
v___x_1046_ = v___x_1037_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_del_object(v___x_1032_);
lean_dec(v_snd_1030_);
lean_dec(v_fst_1029_);
lean_dec(v___x_1026_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
v_a_1278_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1034_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1034_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
else
{
lean_dec(v___x_1026_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_fn_1023_);
return v___x_1027_;
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v_e_1010_);
v___x_1287_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1288_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1287_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1288_;
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v_e_1010_);
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1291_, lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1291_, v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec(v_i_1291_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1304_, lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1304_, v_e_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_fst_1321_; lean_object* v___x_1323_; 
v_fst_1321_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_fst_1321_);
lean_dec(v_a_1317_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v_fst_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_fst_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1316_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1334_, lean_object* v_e_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1334_, v_e_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec(v_n_1334_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1347_, lean_object* v_prefixSize_1348_, lean_object* v_suffixSize_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_numArgs_1360_; uint8_t v___x_1361_; 
v_numArgs_1360_ = l_Lean_Expr_getAppNumArgs(v_e_1347_);
v___x_1361_ = lean_nat_dec_le(v_numArgs_1360_, v_prefixSize_1348_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_nat_add(v_prefixSize_1348_, v_suffixSize_1349_);
v___x_1363_ = lean_nat_dec_lt(v___x_1362_, v_numArgs_1360_);
lean_dec(v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_suffixSize_1349_);
v___x_1364_ = lean_nat_sub(v_numArgs_1360_, v_prefixSize_1348_);
lean_dec(v_numArgs_1360_);
v___x_1365_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1364_, v_e_1347_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v___x_1364_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = lean_nat_sub(v_numArgs_1360_, v_prefixSize_1348_);
lean_dec(v_numArgs_1360_);
v___x_1367_ = lean_nat_sub(v___x_1366_, v_suffixSize_1349_);
lean_dec(v___x_1366_);
v___x_1368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1368_, 0, v_suffixSize_1349_);
v___x_1369_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1368_, v_e_1347_, v___x_1367_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v___x_1367_);
return v___x_1369_;
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v_numArgs_1360_);
lean_dec(v_suffixSize_1349_);
lean_dec_ref(v_e_1347_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1372_, lean_object* v_prefixSize_1373_, lean_object* v_suffixSize_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1372_, v_prefixSize_1373_, v_suffixSize_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec(v_prefixSize_1373_);
return v_res_1385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1388_ = lean_unsigned_to_nat(13u);
v___x_1389_ = lean_unsigned_to_nat(312u);
v___x_1390_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1392_ = l_mkPanicMessageWithDecl(v___x_1391_, v___x_1390_, v___x_1389_, v___x_1388_, v___x_1387_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1393_, lean_object* v_i_1394_, lean_object* v_e_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_nat_dec_eq(v_i_1394_, v___x_1406_);
if (v___x_1407_ == 0)
{
if (lean_obj_tag(v_e_1395_) == 5)
{
lean_object* v_fn_1408_; lean_object* v_arg_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_fn_1408_ = lean_ctor_get(v_e_1395_, 0);
lean_inc_ref_n(v_fn_1408_, 2);
v_arg_1409_ = lean_ctor_get(v_e_1395_, 1);
lean_inc_ref(v_arg_1409_);
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_nat_sub(v_i_1394_, v___x_1410_);
v___x_1412_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1393_, v___x_1411_, v_fn_1408_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1432_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1432_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1432_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = lean_array_fget_borrowed(v_rewritable_1393_, v___x_1411_);
lean_dec(v___x_1411_);
v___x_1418_ = lean_unbox(v___x_1417_);
if (v___x_1418_ == 0)
{
if (lean_obj_tag(v_a_1413_) == 0)
{
uint8_t v_contextDependent_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_dec_ref(v_arg_1409_);
lean_dec_ref_known(v_e_1395_, 2);
lean_dec_ref(v_fn_1408_);
v_contextDependent_1419_ = lean_ctor_get_uint8(v_a_1413_, 1);
lean_dec_ref_known(v_a_1413_, 0);
v___x_1420_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1419_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1420_);
v___x_1422_ = v___x_1415_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
lean_object* v_e_x27_1424_; lean_object* v_proof_1425_; uint8_t v_contextDependent_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1415_);
v_e_x27_1424_ = lean_ctor_get(v_a_1413_, 0);
lean_inc_ref(v_e_x27_1424_);
v_proof_1425_ = lean_ctor_get(v_a_1413_, 1);
lean_inc_ref(v_proof_1425_);
v_contextDependent_1426_ = lean_ctor_get_uint8(v_a_1413_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1413_, 2);
v___x_1427_ = lean_unbox(v___x_1417_);
v___x_1428_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1395_, v_fn_1408_, v_arg_1409_, v_e_x27_1424_, v_proof_1425_, v___x_1427_, v_contextDependent_1426_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1428_;
}
}
else
{
lean_object* v___x_1429_; 
lean_del_object(v___x_1415_);
lean_inc(v_a_1404_);
lean_inc_ref(v_a_1403_);
lean_inc(v_a_1402_);
lean_inc_ref(v_a_1401_);
lean_inc(v_a_1400_);
lean_inc_ref(v_a_1399_);
lean_inc(v_a_1398_);
lean_inc_ref(v_a_1397_);
lean_inc(v_a_1396_);
lean_inc_ref(v_arg_1409_);
v___x_1429_ = lean_sym_simp(v_arg_1409_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1395_, v_fn_1408_, v_arg_1409_, v_a_1413_, v_a_1430_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1431_;
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref(v_arg_1409_);
lean_dec_ref(v_fn_1408_);
lean_dec_ref_known(v_e_1395_, 2);
return v___x_1429_;
}
}
}
}
else
{
lean_dec(v___x_1411_);
lean_dec_ref(v_arg_1409_);
lean_dec_ref(v_fn_1408_);
lean_dec_ref_known(v_e_1395_, 2);
return v___x_1412_;
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec_ref(v_e_1395_);
v___x_1433_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1434_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1433_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1434_;
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v_e_1395_);
v___x_1435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1437_, lean_object* v_i_1438_, lean_object* v_e_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1437_, v_i_1438_, v_e_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec(v_i_1438_);
lean_dec_ref(v_rewritable_1437_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1451_, lean_object* v_i_1452_, lean_object* v_e_1453_, lean_object* v_h_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1451_, v_i_1452_, v_e_1453_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1466_, lean_object* v_i_1467_, lean_object* v_e_1468_, lean_object* v_h_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1466_, v_i_1467_, v_e_1468_, v_h_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec(v_i_1467_);
lean_dec_ref(v_rewritable_1466_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1481_, lean_object* v___x_1482_, lean_object* v_x_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1481_, v___x_1482_, v_x_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1495_, lean_object* v___x_1496_, lean_object* v_x_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1495_, v___x_1496_, v_x_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec(v___x_1496_);
lean_dec_ref(v_rewritable_1495_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1509_, lean_object* v_rewritable_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_numArgs_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_numArgs_1521_ = l_Lean_Expr_getAppNumArgs(v_e_1509_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_nat_dec_eq(v_numArgs_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_array_get_size(v_rewritable_1510_);
v___x_1525_ = lean_nat_dec_lt(v___x_1524_, v_numArgs_1521_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1510_, v_numArgs_1521_, v_e_1509_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
lean_dec(v_numArgs_1521_);
lean_dec_ref(v_rewritable_1510_);
return v___x_1526_;
}
else
{
lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1527_, 0, v_rewritable_1510_);
lean_closure_set(v___f_1527_, 1, v___x_1524_);
v___x_1528_ = lean_nat_sub(v_numArgs_1521_, v___x_1524_);
lean_dec(v_numArgs_1521_);
v___x_1529_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1527_, v_e_1509_, v___x_1528_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
lean_dec(v___x_1528_);
return v___x_1529_;
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_numArgs_1521_);
lean_dec_ref(v_rewritable_1510_);
lean_dec_ref(v_e_1509_);
v___x_1530_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1532_, lean_object* v_rewritable_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1532_, v_rewritable_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1545_, lean_object* v_numEqs_1546_, lean_object* v_result_1547_){
_start:
{
if (lean_obj_tag(v_result_1547_) == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
lean_dec(v_numEqs_1546_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_array_get_size(v_argResults_1545_);
v___x_1550_ = lean_nat_dec_lt(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec_ref_known(v_result_1547_, 0);
return v_argResults_1545_;
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_array_push(v_argResults_1545_, v_result_1547_);
return v___x_1551_;
}
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_argResults_1545_);
v___x_1553_ = lean_nat_dec_lt(v___x_1552_, v_numEqs_1546_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_numEqs_1546_);
v___x_1554_ = lean_array_push(v_argResults_1545_, v_result_1547_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v_argResults_1545_);
v___x_1555_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1556_ = lean_mk_array(v_numEqs_1546_, v___x_1555_);
v___x_1557_ = lean_array_push(v___x_1556_, v_result_1547_);
return v___x_1557_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1560_ = lean_unsigned_to_nat(13u);
v___x_1561_ = lean_unsigned_to_nat(433u);
v___x_1562_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1564_ = l_mkPanicMessageWithDecl(v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_, v___x_1559_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1565_, lean_object* v_mkNonRflResult_1566_, lean_object* v_e_1567_, lean_object* v_i_1568_, lean_object* v_numEqs_1569_, lean_object* v_argResults_1570_, uint8_t v_anyCD_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
if (lean_obj_tag(v_e_1567_) == 5)
{
lean_object* v_fn_1582_; lean_object* v_arg_1583_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v_fn_1582_ = lean_ctor_get(v_e_1567_, 0);
lean_inc_ref(v_fn_1582_);
v_arg_1583_ = lean_ctor_get(v_e_1567_, 1);
lean_inc_ref(v_arg_1583_);
lean_dec_ref_known(v_e_1567_, 2);
v___x_1597_ = 0;
v___x_1598_ = lean_box(v___x_1597_);
v___x_1599_ = lean_array_get(v___x_1598_, v_argKinds_1565_, v_i_1568_);
lean_dec(v___x_1598_);
v___x_1600_ = lean_unbox(v___x_1599_);
lean_dec(v___x_1599_);
switch(v___x_1600_)
{
case 5:
{
lean_dec_ref(v_arg_1583_);
v___y_1585_ = v_a_1572_;
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
v___y_1593_ = v_a_1580_;
goto v___jp_1584_;
}
case 0:
{
lean_dec_ref(v_arg_1583_);
v___y_1585_ = v_a_1572_;
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
v___y_1593_ = v_a_1580_;
goto v___jp_1584_;
}
case 3:
{
lean_dec_ref(v_arg_1583_);
v___y_1585_ = v_a_1572_;
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
v___y_1593_ = v_a_1580_;
goto v___jp_1584_;
}
case 2:
{
lean_object* v___x_1601_; 
lean_inc(v_a_1580_);
lean_inc_ref(v_a_1579_);
lean_inc(v_a_1578_);
lean_inc_ref(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc_ref(v_a_1575_);
lean_inc(v_a_1574_);
lean_inc_ref(v_a_1573_);
lean_inc(v_a_1572_);
v___x_1601_ = lean_sym_simp(v_arg_1583_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_n(v_a_1602_, 2);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_sub(v_i_1568_, v___x_1603_);
lean_dec(v_i_1568_);
v___x_1605_ = lean_nat_add(v_numEqs_1569_, v___x_1603_);
v___x_1606_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1570_, v_numEqs_1569_, v_a_1602_);
if (v_anyCD_1571_ == 0)
{
if (lean_obj_tag(v_a_1602_) == 0)
{
uint8_t v_contextDependent_1607_; 
v_contextDependent_1607_ = lean_ctor_get_uint8(v_a_1602_, 1);
lean_dec_ref_known(v_a_1602_, 0);
v_e_1567_ = v_fn_1582_;
v_i_1568_ = v___x_1604_;
v_numEqs_1569_ = v___x_1605_;
v_argResults_1570_ = v___x_1606_;
v_anyCD_1571_ = v_contextDependent_1607_;
goto _start;
}
else
{
uint8_t v_contextDependent_1609_; 
v_contextDependent_1609_ = lean_ctor_get_uint8(v_a_1602_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1602_, 2);
v_e_1567_ = v_fn_1582_;
v_i_1568_ = v___x_1604_;
v_numEqs_1569_ = v___x_1605_;
v_argResults_1570_ = v___x_1606_;
v_anyCD_1571_ = v_contextDependent_1609_;
goto _start;
}
}
else
{
lean_dec(v_a_1602_);
v_e_1567_ = v_fn_1582_;
v_i_1568_ = v___x_1604_;
v_numEqs_1569_ = v___x_1605_;
v_argResults_1570_ = v___x_1606_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_1582_);
lean_dec_ref(v_argResults_1570_);
lean_dec(v_numEqs_1569_);
lean_dec(v_i_1568_);
lean_dec_ref(v_mkNonRflResult_1566_);
return v___x_1601_;
}
}
default: 
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_fn_1582_);
lean_dec_ref(v_argResults_1570_);
lean_dec(v_numEqs_1569_);
lean_dec(v_i_1568_);
lean_dec_ref(v_mkNonRflResult_1566_);
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1613_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1612_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1613_;
}
}
v___jp_1584_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = lean_nat_sub(v_i_1568_, v___x_1594_);
lean_dec(v_i_1568_);
v_e_1567_ = v_fn_1582_;
v_i_1568_ = v___x_1595_;
v_a_1572_ = v___y_1585_;
v_a_1573_ = v___y_1586_;
v_a_1574_ = v___y_1587_;
v_a_1575_ = v___y_1588_;
v_a_1576_ = v___y_1589_;
v_a_1577_ = v___y_1590_;
v_a_1578_ = v___y_1591_;
v_a_1579_ = v___y_1592_;
v_a_1580_ = v___y_1593_;
goto _start;
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
lean_dec(v_numEqs_1569_);
lean_dec(v_i_1568_);
lean_dec_ref(v_e_1567_);
v___x_1614_ = lean_array_get_size(v_argResults_1570_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_nat_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = l_Array_reverse___redArg(v_argResults_1570_);
lean_inc(v_a_1580_);
lean_inc_ref(v_a_1579_);
lean_inc(v_a_1578_);
lean_inc_ref(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc_ref(v_a_1575_);
lean_inc(v_a_1574_);
lean_inc_ref(v_a_1573_);
lean_inc(v_a_1572_);
v___x_1618_ = lean_apply_11(v_mkNonRflResult_1566_, v___x_1617_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, lean_box(0));
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
if (v_anyCD_1571_ == 0)
{
lean_dec(v_a_1619_);
return v___x_1618_;
}
else
{
if (lean_obj_tag(v_a_1619_) == 0)
{
uint8_t v_contextDependent_1623_; 
v_contextDependent_1623_ = lean_ctor_get_uint8(v_a_1619_, 1);
if (v_contextDependent_1623_ == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
goto v___jp_1620_;
}
else
{
lean_dec_ref_known(v_a_1619_, 0);
return v___x_1618_;
}
}
else
{
uint8_t v_contextDependent_1624_; 
v_contextDependent_1624_ = lean_ctor_get_uint8(v_a_1619_, sizeof(void*)*2 + 1);
if (v_contextDependent_1624_ == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
goto v___jp_1620_;
}
else
{
lean_dec_ref_known(v_a_1619_, 2);
return v___x_1618_;
}
}
}
v___jp_1620_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1619_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
else
{
return v___x_1618_;
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec_ref(v_argResults_1570_);
lean_dec_ref(v_mkNonRflResult_1566_);
v___x_1625_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_1571_);
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object** _args){
lean_object* v_argKinds_1627_ = _args[0];
lean_object* v_mkNonRflResult_1628_ = _args[1];
lean_object* v_e_1629_ = _args[2];
lean_object* v_i_1630_ = _args[3];
lean_object* v_numEqs_1631_ = _args[4];
lean_object* v_argResults_1632_ = _args[5];
lean_object* v_anyCD_1633_ = _args[6];
lean_object* v_a_1634_ = _args[7];
lean_object* v_a_1635_ = _args[8];
lean_object* v_a_1636_ = _args[9];
lean_object* v_a_1637_ = _args[10];
lean_object* v_a_1638_ = _args[11];
lean_object* v_a_1639_ = _args[12];
lean_object* v_a_1640_ = _args[13];
lean_object* v_a_1641_ = _args[14];
lean_object* v_a_1642_ = _args[15];
lean_object* v_a_1643_ = _args[16];
_start:
{
uint8_t v_anyCD_boxed_1644_; lean_object* v_res_1645_; 
v_anyCD_boxed_1644_ = lean_unbox(v_anyCD_1633_);
v_res_1645_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1627_, v_mkNonRflResult_1628_, v_e_1629_, v_i_1630_, v_numEqs_1631_, v_argResults_1632_, v_anyCD_boxed_1644_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_argKinds_1627_);
return v_res_1645_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* v_msg_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_17246__overap_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
v___x_17246__overap_1659_ = lean_panic_fn_borrowed(v___x_1658_, v_msg_1647_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
v___x_1660_ = lean_apply_10(v___x_17246__overap_1659_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, lean_box(0));
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* v_msg_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
return v_res_1672_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(uint8_t v___x_1673_, lean_object* v_as_1674_, size_t v_i_1675_, size_t v_stop_1676_){
_start:
{
uint8_t v___x_1681_; 
v___x_1681_ = lean_usize_dec_eq(v_i_1675_, v_stop_1676_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = lean_array_uget_borrowed(v_as_1674_, v_i_1675_);
v___x_1683_ = lean_unbox(v___x_1682_);
if (v___x_1683_ == 3)
{
if (v___x_1673_ == 0)
{
goto v___jp_1677_;
}
else
{
return v___x_1673_;
}
}
else
{
goto v___jp_1677_;
}
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = 0;
return v___x_1684_;
}
v___jp_1677_:
{
size_t v___x_1678_; size_t v___x_1679_; 
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1675_, v___x_1678_);
v_i_1675_ = v___x_1679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object* v___x_1685_, lean_object* v_as_1686_, lean_object* v_i_1687_, lean_object* v_stop_1688_){
_start:
{
uint8_t v___x_19065__boxed_1689_; size_t v_i_boxed_1690_; size_t v_stop_boxed_1691_; uint8_t v_res_1692_; lean_object* v_r_1693_; 
v___x_19065__boxed_1689_ = lean_unbox(v___x_1685_);
v_i_boxed_1690_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_stop_boxed_1691_ = lean_unbox_usize(v_stop_1688_);
lean_dec(v_stop_1688_);
v_res_1692_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_19065__boxed_1689_, v_as_1686_, v_i_boxed_1690_, v_stop_boxed_1691_);
lean_dec_ref(v_as_1686_);
v_r_1693_ = lean_box(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object* v_as_1694_, size_t v_i_1695_, size_t v_stop_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_usize_dec_eq(v_i_1695_, v_stop_1696_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; uint8_t v___y_1700_; lean_object* v___x_1704_; 
v___x_1698_ = 1;
v___x_1704_ = lean_array_uget_borrowed(v_as_1694_, v_i_1695_);
if (lean_obj_tag(v___x_1704_) == 0)
{
uint8_t v_contextDependent_1705_; 
v_contextDependent_1705_ = lean_ctor_get_uint8(v___x_1704_, 1);
v___y_1700_ = v_contextDependent_1705_;
goto v___jp_1699_;
}
else
{
uint8_t v_contextDependent_1706_; 
v_contextDependent_1706_ = lean_ctor_get_uint8(v___x_1704_, sizeof(void*)*2 + 1);
v___y_1700_ = v_contextDependent_1706_;
goto v___jp_1699_;
}
v___jp_1699_:
{
if (v___y_1700_ == 0)
{
size_t v___x_1701_; size_t v___x_1702_; 
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1695_, v___x_1701_);
v_i_1695_ = v___x_1702_;
goto _start;
}
else
{
return v___x_1698_;
}
}
}
else
{
uint8_t v___x_1707_; 
v___x_1707_ = 0;
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v_as_1708_, lean_object* v_i_1709_, lean_object* v_stop_1710_){
_start:
{
size_t v_i_boxed_1711_; size_t v_stop_boxed_1712_; uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_i_boxed_1711_ = lean_unbox_usize(v_i_1709_);
lean_dec(v_i_1709_);
v_stop_boxed_1712_ = lean_unbox_usize(v_stop_1710_);
lean_dec(v_stop_1710_);
v_res_1713_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1708_, v_i_boxed_1711_, v_stop_boxed_1712_);
lean_dec_ref(v_as_1708_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1717_ = lean_unsigned_to_nat(13u);
v___x_1718_ = lean_unsigned_to_nat(405u);
v___x_1719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1721_ = l_mkPanicMessageWithDecl(v___x_1720_, v___x_1719_, v___x_1718_, v___x_1717_, v___x_1716_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1722_, lean_object* v_as_1723_, size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_a_1738_; uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_b_1726_);
return v___x_1743_;
}
else
{
lean_object* v_snd_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1939_; 
v_snd_1744_ = lean_ctor_get(v_b_1726_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_b_1726_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v_b_1726_, 0);
lean_dec(v_unused_1940_);
v___x_1746_ = v_b_1726_;
v_isShared_1747_ = v_isSharedCheck_1939_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_snd_1744_);
lean_dec(v_b_1726_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1939_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v_snd_1748_; lean_object* v_snd_1749_; lean_object* v_snd_1750_; lean_object* v_snd_1751_; lean_object* v_fst_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1937_; 
v_snd_1748_ = lean_ctor_get(v_snd_1744_, 1);
lean_inc(v_snd_1748_);
v_snd_1749_ = lean_ctor_get(v_snd_1748_, 1);
lean_inc(v_snd_1749_);
v_snd_1750_ = lean_ctor_get(v_snd_1749_, 1);
lean_inc(v_snd_1750_);
v_snd_1751_ = lean_ctor_get(v_snd_1750_, 1);
lean_inc(v_snd_1751_);
v_fst_1752_ = lean_ctor_get(v_snd_1744_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_snd_1744_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_snd_1744_, 1);
lean_dec(v_unused_1938_);
v___x_1754_ = v_snd_1744_;
v_isShared_1755_ = v_isSharedCheck_1937_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_fst_1752_);
lean_dec(v_snd_1744_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1937_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_fst_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1935_; 
v_fst_1756_ = lean_ctor_get(v_snd_1748_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_snd_1748_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; 
v_unused_1936_ = lean_ctor_get(v_snd_1748_, 1);
lean_dec(v_unused_1936_);
v___x_1758_ = v_snd_1748_;
v_isShared_1759_ = v_isSharedCheck_1935_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_fst_1756_);
lean_dec(v_snd_1748_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1935_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_fst_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1933_; 
v_fst_1760_ = lean_ctor_get(v_snd_1749_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_snd_1749_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v_snd_1749_, 1);
lean_dec(v_unused_1934_);
v___x_1762_ = v_snd_1749_;
v_isShared_1763_ = v_isSharedCheck_1933_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_fst_1760_);
lean_dec(v_snd_1749_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1933_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_fst_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1931_; 
v_fst_1764_ = lean_ctor_get(v_snd_1750_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_snd_1750_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_snd_1750_, 1);
lean_dec(v_unused_1932_);
v___x_1766_ = v_snd_1750_;
v_isShared_1767_ = v_isSharedCheck_1931_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_fst_1764_);
lean_dec(v_snd_1750_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1931_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_array_1768_; lean_object* v_start_1769_; lean_object* v_stop_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_array_1768_ = lean_ctor_get(v_snd_1751_, 0);
v_start_1769_ = lean_ctor_get(v_snd_1751_, 1);
v_stop_1770_ = lean_ctor_get(v_snd_1751_, 2);
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_nat_dec_lt(v_start_1769_, v_stop_1770_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1774_; 
if (v_isShared_1767_ == 0)
{
v___x_1774_ = v___x_1766_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_fst_1764_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_snd_1751_);
v___x_1774_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1774_);
v___x_1776_ = v___x_1762_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_fst_1760_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 1, v___x_1776_);
v___x_1778_ = v___x_1758_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_fst_1756_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v___x_1778_);
v___x_1780_ = v___x_1754_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fst_1752_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1780_);
lean_ctor_set(v___x_1746_, 0, v___x_1771_);
v___x_1782_ = v___x_1746_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
}
}
}
}
else
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1927_; 
lean_inc(v_stop_1770_);
lean_inc(v_start_1769_);
lean_inc_ref(v_array_1768_);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_snd_1751_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; lean_object* v_unused_1929_; lean_object* v_unused_1930_; 
v_unused_1928_ = lean_ctor_get(v_snd_1751_, 2);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_snd_1751_, 1);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_snd_1751_, 0);
lean_dec(v_unused_1930_);
v___x_1790_ = v_snd_1751_;
v_isShared_1791_ = v_isSharedCheck_1927_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_snd_1751_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1927_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v_a_1792_ = lean_array_uget_borrowed(v_as_1723_, v_i_1725_);
v___x_1793_ = lean_array_fget(v_array_1768_, v_start_1769_);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_add(v_start_1769_, v___x_1794_);
lean_dec(v_start_1769_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v___x_1795_);
v___x_1797_ = v___x_1790_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_array_1768_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_stop_1770_);
v___x_1797_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_proof_1801_; lean_object* v_subst_1802_; uint8_t v___x_1828_; 
lean_inc(v_a_1792_);
v___x_1798_ = l_Lean_Expr_app___override(v_fst_1752_, v_a_1792_);
v___x_1799_ = l_Lean_Expr_bindingBody_x21(v_fst_1756_);
lean_dec(v_fst_1756_);
v___x_1828_ = lean_unbox(v___x_1793_);
lean_dec(v___x_1793_);
switch(v___x_1828_)
{
case 0:
{
lean_del_object(v___x_1766_);
lean_del_object(v___x_1762_);
lean_del_object(v___x_1758_);
lean_del_object(v___x_1754_);
lean_del_object(v___x_1746_);
goto v___jp_1821_;
}
case 3:
{
lean_del_object(v___x_1766_);
lean_del_object(v___x_1762_);
lean_del_object(v___x_1758_);
lean_del_object(v___x_1754_);
lean_del_object(v___x_1746_);
goto v___jp_1821_;
}
case 5:
{
lean_object* v___x_1829_; lean_object* v_instNew_1831_; lean_object* v___x_1840_; 
lean_del_object(v___x_1766_);
lean_del_object(v___x_1762_);
lean_del_object(v___x_1758_);
lean_del_object(v___x_1754_);
lean_del_object(v___x_1746_);
lean_inc_n(v_a_1792_, 2);
v___x_1829_ = lean_array_push(v_fst_1764_, v_a_1792_);
v___x_1840_ = l_Lean_Meta_Sym_inferType(v_a_1792_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l_Lean_Expr_bindingDomain_x21(v___x_1799_);
v___x_1843_ = lean_expr_instantiate_rev(v___x_1842_, v___x_1829_);
lean_dec_ref(v___x_1842_);
lean_inc_ref(v___x_1843_);
v___x_1844_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_1841_, v___x_1843_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; uint8_t v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = lean_unbox(v_a_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Meta_trySynthInstance(v___x_1843_, v___x_1771_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1865_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1865_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1865_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
if (lean_obj_tag(v_a_1848_) == 1)
{
lean_object* v_a_1852_; 
lean_del_object(v___x_1850_);
lean_dec(v_a_1845_);
v_a_1852_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v_a_1848_, 1);
v_instNew_1831_ = v_a_1852_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1853_; uint8_t v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec(v_a_1848_);
v___x_1853_ = lean_alloc_ctor(0, 0, 2);
v___x_1854_ = lean_unbox(v_a_1845_);
lean_ctor_set_uint8(v___x_1853_, 0, v___x_1854_);
v___x_1855_ = lean_unbox(v_a_1845_);
lean_dec(v_a_1845_);
lean_ctor_set_uint8(v___x_1853_, 1, v___x_1855_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1853_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1829_);
lean_ctor_set(v___x_1857_, 1, v___x_1797_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_fst_1760_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1799_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1798_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1856_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1861_);
v___x_1863_ = v___x_1850_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1845_);
lean_dec_ref(v___x_1829_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec_ref(v___x_1797_);
lean_dec(v_fst_1760_);
v_a_1866_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1847_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1847_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_dec(v_a_1845_);
lean_dec_ref(v___x_1843_);
lean_inc(v_a_1792_);
v_instNew_1831_ = v_a_1792_;
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v___x_1843_);
lean_dec_ref(v___x_1829_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec_ref(v___x_1797_);
lean_dec(v_fst_1760_);
v_a_1874_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1844_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1844_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___x_1829_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec_ref(v___x_1797_);
lean_dec(v_fst_1760_);
v_a_1882_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1840_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1840_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
v___jp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_inc_ref(v_instNew_1831_);
v___x_1832_ = l_Lean_Expr_app___override(v___x_1798_, v_instNew_1831_);
v___x_1833_ = lean_array_push(v___x_1829_, v_instNew_1831_);
v___x_1834_ = l_Lean_Expr_bindingBody_x21(v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1797_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_fst_1760_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1834_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1832_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1771_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v_a_1738_ = v___x_1839_;
goto v___jp_1737_;
}
}
case 2:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1792_);
v___x_1891_ = lean_array_push(v_fst_1764_, v_a_1792_);
v___x_1892_ = lean_array_get_borrowed(v___x_1890_, v_argResults_1722_, v_fst_1760_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; 
lean_inc(v_a_1792_);
v___x_1893_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1792_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_n(v_a_1894_, 2);
lean_dec_ref_known(v___x_1893_, 1);
lean_inc_n(v_a_1792_, 2);
v___x_1895_ = l_Lean_mkAppB(v___x_1798_, v_a_1792_, v_a_1894_);
v___x_1896_ = lean_array_push(v___x_1891_, v_a_1792_);
v___x_1897_ = lean_array_push(v___x_1896_, v_a_1894_);
v_proof_1801_ = v___x_1895_;
v_subst_1802_ = v___x_1897_;
goto v___jp_1800_;
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v___x_1891_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec_ref(v___x_1797_);
lean_del_object(v___x_1766_);
lean_del_object(v___x_1762_);
lean_dec(v_fst_1760_);
lean_del_object(v___x_1758_);
lean_del_object(v___x_1754_);
lean_del_object(v___x_1746_);
v_a_1898_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1893_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1893_);
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
lean_object* v_e_x27_1906_; lean_object* v_proof_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_e_x27_1906_ = lean_ctor_get(v___x_1892_, 0);
v_proof_1907_ = lean_ctor_get(v___x_1892_, 1);
lean_inc_ref_n(v_proof_1907_, 2);
lean_inc_ref_n(v_e_x27_1906_, 2);
v___x_1908_ = l_Lean_mkAppB(v___x_1798_, v_e_x27_1906_, v_proof_1907_);
v___x_1909_ = lean_array_push(v___x_1891_, v_e_x27_1906_);
v___x_1910_ = lean_array_push(v___x_1909_, v_proof_1907_);
v_proof_1801_ = v___x_1908_;
v_subst_1802_ = v___x_1910_;
goto v___jp_1800_;
}
}
default: 
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1766_);
lean_del_object(v___x_1762_);
lean_del_object(v___x_1758_);
lean_del_object(v___x_1754_);
lean_del_object(v___x_1746_);
v___x_1911_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
v___x_1912_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_1911_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1912_, 1);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_fst_1764_);
lean_ctor_set(v___x_1913_, 1, v___x_1797_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_fst_1760_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1799_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1798_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1771_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v_a_1738_ = v___x_1917_;
goto v___jp_1737_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec_ref(v___x_1797_);
lean_dec(v_fst_1764_);
lean_dec(v_fst_1760_);
v_a_1918_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1912_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1912_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
v___jp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1803_ = l_Lean_Expr_bindingBody_x21(v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1804_ = l_Lean_Expr_bindingBody_x21(v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_nat_add(v_fst_1760_, v___x_1794_);
lean_dec(v_fst_1760_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1797_);
lean_ctor_set(v___x_1766_, 0, v_subst_1802_);
v___x_1807_ = v___x_1766_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_subst_1802_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1797_);
v___x_1807_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1807_);
lean_ctor_set(v___x_1762_, 0, v___x_1805_);
v___x_1809_ = v___x_1762_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 1, v___x_1809_);
lean_ctor_set(v___x_1758_, 0, v___x_1804_);
v___x_1811_ = v___x_1758_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v___x_1811_);
lean_ctor_set(v___x_1754_, 0, v_proof_1801_);
v___x_1813_ = v___x_1754_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_proof_1801_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1813_);
lean_ctor_set(v___x_1746_, 0, v___x_1771_);
v___x_1815_ = v___x_1746_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
v_a_1738_ = v___x_1815_;
goto v___jp_1737_;
}
}
}
}
}
}
v___jp_1821_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_inc(v_a_1792_);
v___x_1822_ = lean_array_push(v_fst_1764_, v_a_1792_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1797_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_fst_1760_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1799_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1798_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1771_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v_a_1738_ = v___x_1827_;
goto v___jp_1737_;
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
v___jp_1737_:
{
size_t v___x_1739_; size_t v___x_1740_; 
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1725_, v___x_1739_);
v_i_1725_ = v___x_1740_;
v_b_1726_ = v_a_1738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_1941_, lean_object* v_as_1942_, lean_object* v_sz_1943_, lean_object* v_i_1944_, lean_object* v_b_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1943_);
lean_dec(v_sz_1943_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1944_);
lean_dec(v_i_1944_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1941_, v_as_1942_, v_sz_boxed_1956_, v_i_boxed_1957_, v_b_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v_as_1942_);
lean_dec_ref(v_argResults_1941_);
return v_res_1958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1960_ = lean_unsigned_to_nat(34u);
v___x_1961_ = lean_unsigned_to_nat(406u);
v___x_1962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1963_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1964_ = l_mkPanicMessageWithDecl(v___x_1963_, v___x_1962_, v___x_1961_, v___x_1960_, v___x_1959_);
return v___x_1964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1967_; lean_object* v_dummy_1968_; 
v___x_1967_ = lean_box(0);
v_dummy_1968_ = l_Lean_Expr_sort___override(v___x_1967_);
return v_dummy_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_1972_, lean_object* v_argKinds_1973_, lean_object* v_type_1974_, lean_object* v_proof_1975_, lean_object* v_argResults_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v_j_1999_; lean_object* v_subst_2000_; lean_object* v_dummy_2001_; lean_object* v_nargs_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v_args_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; size_t v_sz_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
v_j_1999_ = lean_unsigned_to_nat(0u);
v_subst_2000_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2001_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2002_ = l_Lean_Expr_getAppNumArgs(v_e_1972_);
lean_inc(v_nargs_2002_);
v___x_2003_ = lean_mk_array(v_nargs_2002_, v_dummy_2001_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = lean_nat_sub(v_nargs_2002_, v___x_2004_);
lean_dec(v_nargs_2002_);
v_args_2006_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1972_, v___x_2003_, v___x_2005_);
v___x_2007_ = lean_array_get_size(v_argKinds_1973_);
lean_inc_ref(v_argKinds_1973_);
v___x_2008_ = l_Array_toSubarray___redArg(v_argKinds_1973_, v_j_1999_, v___x_2007_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_subst_2000_);
lean_ctor_set(v___x_2010_, 1, v___x_2008_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_j_1999_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_type_1974_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_proof_1975_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2009_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v_sz_2015_ = lean_array_size(v_args_2006_);
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1976_, v_args_2006_, v_sz_2015_, v___x_2016_, v___x_2014_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec_ref(v_args_2006_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2088_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2088_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2088_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_fst_2022_; 
v_fst_2022_ = lean_ctor_get(v_a_2018_, 0);
if (lean_obj_tag(v_fst_2022_) == 0)
{
lean_object* v_snd_2023_; lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v___y_2027_; uint8_t v___y_2028_; lean_object* v_rhs_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_snd_2023_ = lean_ctor_get(v_a_2018_, 1);
lean_inc(v_snd_2023_);
lean_dec(v_a_2018_);
v_fst_2024_ = lean_ctor_get(v_snd_2023_, 0);
lean_inc(v_fst_2024_);
v_snd_2025_ = lean_ctor_get(v_snd_2023_, 1);
lean_inc(v_snd_2025_);
lean_dec(v_snd_2023_);
v_fst_2056_ = lean_ctor_get(v_snd_2025_, 0);
lean_inc(v_fst_2056_);
v_snd_2057_ = lean_ctor_get(v_snd_2025_, 1);
lean_inc(v_snd_2057_);
lean_dec(v_snd_2025_);
v___x_2058_ = l_Lean_Expr_cleanupAnnotations(v_fst_2056_);
v___x_2059_ = l_Lean_Expr_isApp(v___x_2058_);
if (v___x_2059_ == 0)
{
lean_dec_ref(v___x_2058_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2024_);
lean_del_object(v___x_2020_);
lean_dec_ref(v_argKinds_1973_);
v___y_1988_ = v___y_1977_;
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
goto v___jp_1987_;
}
else
{
lean_object* v_arg_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_arg_2060_ = lean_ctor_get(v___x_2058_, 1);
lean_inc_ref(v_arg_2060_);
v___x_2061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2058_);
v___x_2062_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2024_);
lean_del_object(v___x_2020_);
lean_dec_ref(v_argKinds_1973_);
v___y_1988_ = v___y_1977_;
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2061_);
v___x_2064_ = l_Lean_Expr_isApp(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v___x_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2024_);
lean_del_object(v___x_2020_);
lean_dec_ref(v_argKinds_1973_);
v___y_1988_ = v___y_1977_;
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2063_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2067_ = l_Lean_Expr_isConstOf(v___x_2065_, v___x_2066_);
lean_dec_ref(v___x_2065_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v_arg_2060_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2024_);
lean_del_object(v___x_2020_);
lean_dec_ref(v_argKinds_1973_);
v___y_1988_ = v___y_1977_;
v___y_1989_ = v___y_1978_;
v___y_1990_ = v___y_1979_;
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
goto v___jp_1987_;
}
else
{
lean_object* v_snd_2068_; lean_object* v_fst_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_snd_2068_ = lean_ctor_get(v_snd_2057_, 1);
lean_inc(v_snd_2068_);
lean_dec(v_snd_2057_);
v_fst_2069_ = lean_ctor_get(v_snd_2068_, 0);
lean_inc(v_fst_2069_);
lean_dec(v_snd_2068_);
v___x_2070_ = lean_expr_instantiate_rev(v_arg_2060_, v_fst_2069_);
lean_dec(v_fst_2069_);
lean_dec_ref(v_arg_2060_);
v___x_2071_ = lean_nat_dec_lt(v_j_1999_, v___x_2007_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v_argKinds_1973_);
v_rhs_2035_ = v___x_2070_;
v___y_2036_ = v___y_1980_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
goto v___jp_2034_;
}
else
{
if (v___x_2071_ == 0)
{
lean_dec_ref(v_argKinds_1973_);
v_rhs_2035_ = v___x_2070_;
v___y_2036_ = v___y_1980_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
goto v___jp_2034_;
}
else
{
size_t v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = lean_usize_of_nat(v___x_2007_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_2067_, v_argKinds_1973_, v___x_2016_, v___x_2072_);
lean_dec_ref(v_argKinds_1973_);
if (v___x_2073_ == 0)
{
v_rhs_2035_ = v___x_2070_;
v___y_2036_ = v___y_1980_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2070_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v_rhs_2035_ = v_a_2075_;
v___y_2036_ = v___y_1980_;
v___y_2037_ = v___y_1981_;
v___y_2038_ = v___y_1982_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
goto v___jp_2034_;
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_fst_2024_);
lean_del_object(v___x_2020_);
v_a_2076_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2074_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2074_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
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
v___jp_2026_:
{
uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = 0;
v___x_2030_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2030_, 0, v___y_2027_);
lean_ctor_set(v___x_2030_, 1, v_fst_2024_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*2, v___x_2029_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*2 + 1, v___y_2028_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2030_);
v___x_2032_ = v___x_2020_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
v___jp_2034_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Meta_Sym_shareCommonInc(v_rhs_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = lean_array_get_size(v_argResults_1976_);
v___x_2045_ = lean_nat_dec_lt(v_j_1999_, v___x_2044_);
if (v___x_2045_ == 0)
{
v___y_2027_ = v_a_2043_;
v___y_2028_ = v___x_2045_;
goto v___jp_2026_;
}
else
{
if (v___x_2045_ == 0)
{
v___y_2027_ = v_a_2043_;
v___y_2028_ = v___x_2045_;
goto v___jp_2026_;
}
else
{
size_t v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = lean_usize_of_nat(v___x_2044_);
v___x_2047_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_1976_, v___x_2016_, v___x_2046_);
v___y_2027_ = v_a_2043_;
v___y_2028_ = v___x_2047_;
goto v___jp_2026_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_fst_2024_);
lean_del_object(v___x_2020_);
v_a_2048_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2042_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2042_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
else
{
lean_object* v_val_2084_; lean_object* v___x_2086_; 
lean_inc_ref(v_fst_2022_);
lean_dec(v_a_2018_);
lean_dec_ref(v_argKinds_1973_);
v_val_2084_ = lean_ctor_get(v_fst_2022_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v_fst_2022_, 1);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v_val_2084_);
v___x_2086_ = v___x_2020_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_val_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_argKinds_1973_);
v_a_2089_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2017_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2017_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
v___jp_1987_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_1998_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1997_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2097_, lean_object* v_argKinds_2098_, lean_object* v_type_2099_, lean_object* v_proof_2100_, lean_object* v_argResults_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2097_, v_argKinds_2098_, v_type_2099_, v_proof_2100_, v_argResults_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v_argResults_2101_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2113_, lean_object* v_x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2125_, 0, v___x_2113_);
lean_ctor_set_uint8(v___x_2125_, 1, v___x_2113_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2127_, lean_object* v_x_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v___x_19798__boxed_2139_; lean_object* v_res_2140_; 
v___x_19798__boxed_2139_ = lean_unbox(v___x_2127_);
v_res_2140_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_19798__boxed_2139_, v_x_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v_x_2128_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2143_, lean_object* v_argKinds_2144_, lean_object* v_mkNonRflResult_2145_, lean_object* v_x_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_sub(v___x_2143_, v___x_2157_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2161_ = 0;
v___x_2162_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2144_, v_mkNonRflResult_2145_, v_x_2146_, v___x_2158_, v___x_2159_, v___x_2160_, v___x_2161_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2163_, lean_object* v_argKinds_2164_, lean_object* v_mkNonRflResult_2165_, lean_object* v_x_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2163_, v_argKinds_2164_, v_mkNonRflResult_2165_, v_x_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v_argKinds_2164_);
lean_dec(v___x_2163_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2178_, lean_object* v_thm_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_type_2190_; lean_object* v_proof_2191_; lean_object* v_argKinds_2192_; lean_object* v_mkNonRflResult_2193_; lean_object* v_numArgs_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_type_2190_ = lean_ctor_get(v_thm_2179_, 0);
lean_inc_ref(v_type_2190_);
v_proof_2191_ = lean_ctor_get(v_thm_2179_, 1);
lean_inc_ref(v_proof_2191_);
v_argKinds_2192_ = lean_ctor_get(v_thm_2179_, 2);
lean_inc_ref_n(v_argKinds_2192_, 2);
lean_dec_ref(v_thm_2179_);
lean_inc_ref(v_e_2178_);
v_mkNonRflResult_2193_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2193_, 0, v_e_2178_);
lean_closure_set(v_mkNonRflResult_2193_, 1, v_argKinds_2192_);
lean_closure_set(v_mkNonRflResult_2193_, 2, v_type_2190_);
lean_closure_set(v_mkNonRflResult_2193_, 3, v_proof_2191_);
v_numArgs_2194_ = l_Lean_Expr_getAppNumArgs(v_e_2178_);
v___x_2195_ = lean_array_get_size(v_argKinds_2192_);
v___x_2196_ = lean_nat_dec_lt(v___x_2195_, v_numArgs_2194_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; 
v___x_2197_ = lean_nat_dec_lt(v_numArgs_2194_, v___x_2195_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_numArgs_2194_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_sub(v___x_2195_, v___x_2198_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2202_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2192_, v_mkNonRflResult_2193_, v_e_2178_, v___x_2199_, v___x_2200_, v___x_2201_, v___x_2197_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec_ref(v_argKinds_2192_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
lean_dec_ref(v_mkNonRflResult_2193_);
lean_dec_ref(v_argKinds_2192_);
v___x_2203_ = lean_box(v___x_2196_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2204_, 0, v___x_2203_);
v___x_2205_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2204_, v_e_2178_, v_numArgs_2194_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_numArgs_2194_);
return v___x_2205_;
}
}
else
{
lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___f_2206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2206_, 0, v___x_2195_);
lean_closure_set(v___f_2206_, 1, v_argKinds_2192_);
lean_closure_set(v___f_2206_, 2, v_mkNonRflResult_2193_);
v___x_2207_ = lean_nat_sub(v_numArgs_2194_, v___x_2195_);
lean_dec(v_numArgs_2194_);
v___x_2208_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2206_, v_e_2178_, v___x_2207_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2209_, lean_object* v_thm_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2209_, v_thm_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_f_2233_; lean_object* v___x_2234_; 
v_f_2233_ = l_Lean_Expr_getAppFn(v_e_2222_);
v___x_2234_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2233_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2250_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2250_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2250_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
switch(lean_obj_tag(v_a_2235_))
{
case 0:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec_ref(v_e_2222_);
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
case 1:
{
lean_object* v_prefixSize_2243_; lean_object* v_suffixSize_2244_; lean_object* v___x_2245_; 
lean_del_object(v___x_2237_);
v_prefixSize_2243_ = lean_ctor_get(v_a_2235_, 0);
lean_inc(v_prefixSize_2243_);
v_suffixSize_2244_ = lean_ctor_get(v_a_2235_, 1);
lean_inc(v_suffixSize_2244_);
lean_dec_ref_known(v_a_2235_, 2);
v___x_2245_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2222_, v_prefixSize_2243_, v_suffixSize_2244_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_prefixSize_2243_);
return v___x_2245_;
}
case 2:
{
lean_object* v_rewritable_2246_; lean_object* v___x_2247_; 
lean_del_object(v___x_2237_);
v_rewritable_2246_ = lean_ctor_get(v_a_2235_, 0);
lean_inc_ref(v_rewritable_2246_);
lean_dec_ref_known(v_a_2235_, 1);
v___x_2247_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2222_, v_rewritable_2246_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
return v___x_2247_;
}
default: 
{
lean_object* v_thm_2248_; lean_object* v___x_2249_; 
lean_del_object(v___x_2237_);
v_thm_2248_ = lean_ctor_get(v_a_2235_, 0);
lean_inc_ref(v_thm_2248_);
lean_dec_ref_known(v_a_2235_, 1);
v___x_2249_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2222_, v_thm_2248_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
return v___x_2249_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v_e_2222_);
v_a_2251_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2234_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2234_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
return v_res_2270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2273_ = lean_unsigned_to_nat(55u);
v___x_2274_ = lean_unsigned_to_nat(493u);
v___x_2275_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2276_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2277_ = l_mkPanicMessageWithDecl(v___x_2276_, v___x_2275_, v___x_2274_, v___x_2273_, v___x_2272_);
return v___x_2277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2279_ = lean_unsigned_to_nat(11u);
v___x_2280_ = lean_unsigned_to_nat(501u);
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2283_ = l_mkPanicMessageWithDecl(v___x_2282_, v___x_2281_, v___x_2280_, v___x_2279_, v___x_2278_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2284_, lean_object* v_e_2285_, lean_object* v_i_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
uint8_t v_cd_2298_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = lean_nat_dec_eq(v_i_2286_, v___x_2301_);
if (v___x_2302_ == 0)
{
if (lean_obj_tag(v_e_2285_) == 5)
{
lean_object* v_fn_2303_; lean_object* v_arg_2304_; lean_object* v___x_2305_; lean_object* v_i_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; 
v_fn_2303_ = lean_ctor_get(v_e_2285_, 0);
lean_inc_ref_n(v_fn_2303_, 2);
v_arg_2304_ = lean_ctor_get(v_e_2285_, 1);
lean_inc_ref(v_arg_2304_);
v___x_2305_ = lean_unsigned_to_nat(1u);
v_i_2306_ = lean_nat_sub(v_i_2286_, v___x_2305_);
v___x_2307_ = lean_nat_dec_lt(v_i_2306_, v_stop_2284_);
v___x_2308_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2284_, v_fn_2303_, v_i_2306_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_i_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
if (v___x_2307_ == 0)
{
lean_object* v_a_2309_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
if (lean_obj_tag(v_a_2309_) == 0)
{
uint8_t v_contextDependent_2310_; 
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
v_contextDependent_2310_ = lean_ctor_get_uint8(v_a_2309_, 1);
lean_dec_ref_known(v_a_2309_, 0);
v_cd_2298_ = v_contextDependent_2310_;
goto v___jp_2297_;
}
else
{
lean_object* v_e_x27_2311_; lean_object* v_proof_2312_; uint8_t v_contextDependent_2313_; lean_object* v___x_2314_; 
v_e_x27_2311_ = lean_ctor_get(v_a_2309_, 0);
lean_inc_ref(v_e_x27_2311_);
v_proof_2312_ = lean_ctor_get(v_a_2309_, 1);
lean_inc_ref(v_proof_2312_);
v_contextDependent_2313_ = lean_ctor_get_uint8(v_a_2309_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2309_, 2);
v___x_2314_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2285_, v_fn_2303_, v_arg_2304_, v_e_x27_2311_, v_proof_2312_, v___x_2302_, v_contextDependent_2313_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2314_;
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2308_, 1);
lean_inc_ref(v_fn_2303_);
v___x_2316_ = l_Lean_Meta_Sym_inferType(v_fn_2303_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_Meta_whnfD(v_a_2317_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
if (lean_obj_tag(v_a_2319_) == 7)
{
lean_object* v_binderType_2320_; lean_object* v_body_2321_; uint8_t v___x_2322_; 
v_binderType_2320_ = lean_ctor_get(v_a_2319_, 1);
lean_inc_ref(v_binderType_2320_);
v_body_2321_ = lean_ctor_get(v_a_2319_, 2);
lean_inc_ref(v_body_2321_);
lean_dec_ref_known(v_a_2319_, 3);
v___x_2322_ = l_Lean_Expr_hasLooseBVars(v_body_2321_);
lean_dec_ref(v_body_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Meta_isProp(v_binderType_2320_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; uint8_t v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = lean_unbox(v_a_2324_);
lean_dec(v_a_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
lean_inc_ref(v_a_2292_);
lean_inc(v_a_2291_);
lean_inc_ref(v_a_2290_);
lean_inc(v_a_2289_);
lean_inc_ref(v_a_2288_);
lean_inc(v_a_2287_);
lean_inc_ref(v_arg_2304_);
v___x_2326_ = lean_sym_simp(v_arg_2304_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2285_, v_fn_2303_, v_arg_2304_, v_a_2315_, v_a_2327_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2328_;
}
else
{
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2304_);
lean_dec_ref_known(v_e_2285_, 2);
lean_dec_ref(v_fn_2303_);
return v___x_2326_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2329_, 0, v___x_2302_);
lean_ctor_set_uint8(v___x_2329_, 1, v___x_2302_);
v___x_2330_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2285_, v_fn_2303_, v_arg_2304_, v_a_2315_, v___x_2329_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2330_;
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
v_a_2331_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2323_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2323_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_2320_);
if (lean_obj_tag(v_a_2315_) == 0)
{
uint8_t v_contextDependent_2339_; 
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
v_contextDependent_2339_ = lean_ctor_get_uint8(v_a_2315_, 1);
lean_dec_ref_known(v_a_2315_, 0);
v_cd_2298_ = v_contextDependent_2339_;
goto v___jp_2297_;
}
else
{
lean_object* v_e_x27_2340_; lean_object* v_proof_2341_; uint8_t v_contextDependent_2342_; lean_object* v___x_2343_; 
v_e_x27_2340_ = lean_ctor_get(v_a_2315_, 0);
lean_inc_ref(v_e_x27_2340_);
v_proof_2341_ = lean_ctor_get(v_a_2315_, 1);
lean_inc_ref(v_proof_2341_);
v_contextDependent_2342_ = lean_ctor_get_uint8(v_a_2315_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2315_, 2);
v___x_2343_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2285_, v_fn_2303_, v_arg_2304_, v_e_x27_2340_, v_proof_2341_, v___x_2302_, v_contextDependent_2342_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2343_;
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_a_2319_);
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
v___x_2344_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2345_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2344_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2345_;
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
v_a_2346_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2318_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2318_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
v_a_2354_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2316_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2316_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2304_);
lean_dec_ref(v_fn_2303_);
lean_dec_ref_known(v_e_2285_, 2);
return v___x_2308_;
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref(v_e_2285_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2363_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2362_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2363_;
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec_ref(v_e_2285_);
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
v___jp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_2298_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2366_, lean_object* v_e_2367_, lean_object* v_i_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2366_, v_e_2367_, v_i_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec(v_i_2368_);
lean_dec(v_stop_2366_);
return v_res_2379_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2383_ = lean_unsigned_to_nat(2u);
v___x_2384_ = lean_unsigned_to_nat(476u);
v___x_2385_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2387_ = l_mkPanicMessageWithDecl(v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2388_, lean_object* v_start_2389_, lean_object* v_stop_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = lean_nat_dec_lt(v_start_2389_, v_stop_2390_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v_e_2388_);
v___x_2402_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2403_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2402_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2403_;
}
else
{
lean_object* v_numArgs_2404_; uint8_t v___x_2405_; 
v_numArgs_2404_ = l_Lean_Expr_getAppNumArgs(v_e_2388_);
v___x_2405_ = lean_nat_dec_lt(v_numArgs_2404_, v_start_2389_);
if (v___x_2405_ == 0)
{
lean_object* v_numArgs_2406_; lean_object* v_stop_2407_; lean_object* v___x_2408_; 
v_numArgs_2406_ = lean_nat_sub(v_numArgs_2404_, v_start_2389_);
lean_dec(v_numArgs_2404_);
v_stop_2407_ = lean_nat_sub(v_stop_2390_, v_start_2389_);
v___x_2408_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2407_, v_e_2388_, v_numArgs_2406_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
lean_dec(v_numArgs_2406_);
lean_dec(v_stop_2407_);
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v_numArgs_2404_);
lean_dec_ref(v_e_2388_);
v___x_2409_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2411_, lean_object* v_start_2412_, lean_object* v_stop_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2411_, v_start_2412_, v_stop_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec(v_stop_2413_);
lean_dec(v_start_2412_);
return v_res_2424_;
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
