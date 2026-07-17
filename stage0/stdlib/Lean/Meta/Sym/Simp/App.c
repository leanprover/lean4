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
lean_dec_ref_known(v___x_590_, 1);
lean_inc_ref(v_fn_586_);
v___x_592_ = l_Lean_Meta_Sym_inferType(v_fn_586_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
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
lean_dec_ref_known(v_a_595_, 3);
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
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
v_contextDependent_619_ = lean_ctor_get_uint8(v_a_591_, 1);
lean_dec_ref_known(v_a_591_, 0);
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
lean_dec_ref_known(v_a_591_, 2);
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
lean_dec_ref_known(v___x_602_, 1);
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
lean_dec_ref_known(v___x_605_, 1);
v___x_607_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_572_, v_fn_586_, v_arg_587_, v_a_591_, v_a_606_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_607_;
}
else
{
lean_dec(v_a_591_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
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
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
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
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
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
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
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
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
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
lean_dec_ref(v_fn_586_);
lean_dec_ref_known(v_e_572_, 2);
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
lean_dec_ref_known(v_a_719_, 0);
lean_dec_ref(v_arg_715_);
lean_dec_ref_known(v_e_700_, 2);
lean_dec_ref(v_fn_714_);
return v___x_718_;
}
else
{
lean_object* v_e_x27_720_; lean_object* v_proof_721_; uint8_t v_done_722_; uint8_t v_contextDependent_723_; lean_object* v___x_724_; 
lean_dec_ref_known(v___x_718_, 1);
v_e_x27_720_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_e_x27_720_);
v_proof_721_ = lean_ctor_get(v_a_719_, 1);
lean_inc_ref(v_proof_721_);
v_done_722_ = lean_ctor_get_uint8(v_a_719_, sizeof(void*)*2);
v_contextDependent_723_ = lean_ctor_get_uint8(v_a_719_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_719_, 2);
v___x_724_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_700_, v_fn_714_, v_arg_715_, v_e_x27_720_, v_proof_721_, v_done_722_, v_contextDependent_723_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_724_;
}
}
else
{
lean_dec_ref(v_arg_715_);
lean_dec_ref_known(v_e_700_, 2);
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
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_Lean_Expr_isForall(v_type_773_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_whnfD(v_type_773_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = l_Lean_Expr_isForall(v_a_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v___x_785_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1);
v___x_786_ = l_Lean_MessageData_ofExpr(v_a_783_);
v___x_787_ = l_Lean_indentD(v___x_786_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_785_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_788_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Meta_Sym_shareCommonInc(v_a_783_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_798_;
}
}
else
{
return v___x_782_;
}
}
else
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_type_773_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_808_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_984__overap_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_984__overap_819_ = lean_panic_fn_borrowed(v___x_818_, v_msg_810_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_820_ = lean_apply_7(v___x_984__overap_819_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, lean_box(0));
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_832_ = lean_unsigned_to_nat(47u);
v___x_833_ = lean_unsigned_to_nat(203u);
v___x_834_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_836_ = l_mkPanicMessageWithDecl(v___x_835_, v___x_834_, v___x_833_, v___x_832_, v___x_831_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_837_, lean_object* v_n_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_zero_846_; uint8_t v_isZero_847_; 
v_zero_846_ = lean_unsigned_to_nat(0u);
v_isZero_847_ = lean_nat_dec_eq(v_n_838_, v_zero_846_);
if (v_isZero_847_ == 1)
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_Sym_inferType(v_e_837_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v___x_848_;
}
else
{
lean_object* v_one_849_; lean_object* v_n_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_one_849_ = lean_unsigned_to_nat(1u);
v_n_850_ = lean_nat_sub(v_n_838_, v_one_849_);
v___x_851_ = l_Lean_Expr_appFn_x21(v_e_837_);
lean_dec_ref(v_e_837_);
v___x_852_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_851_, v_n_850_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_n_850_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_853_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
if (lean_obj_tag(v_a_855_) == 7)
{
lean_object* v_body_859_; lean_object* v___x_861_; 
v_body_859_ = lean_ctor_get(v_a_855_, 2);
lean_inc_ref(v_body_859_);
lean_dec_ref_known(v_a_855_, 3);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v_body_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_body_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_del_object(v___x_857_);
lean_dec(v_a_855_);
v___x_863_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_864_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_863_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v___x_864_;
}
}
}
else
{
return v___x_854_;
}
}
else
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_866_, lean_object* v_n_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_866_, v_n_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_n_867_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_876_, lean_object* v_a_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___y_886_; lean_object* v___x_889_; uint8_t v_debug_890_; 
v___x_889_ = lean_st_ref_get(v___y_879_);
v_debug_890_ = lean_ctor_get_uint8(v___x_889_, sizeof(void*)*11);
lean_dec(v___x_889_);
if (v_debug_890_ == 0)
{
v___y_886_ = v___y_879_;
goto v___jp_885_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_876_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_892_; 
lean_dec_ref_known(v___x_891_, 1);
v___x_892_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v___y_886_ = v___y_879_;
goto v___jp_885_;
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v_a_877_);
lean_dec_ref(v_f_876_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_a_877_);
lean_dec_ref(v_f_876_);
v_a_901_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_891_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Lean_Expr_app___override(v_f_876_, v_a_877_);
v___x_888_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_887_, v___y_886_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_909_, lean_object* v_a_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_909_, v_a_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_919_, lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_919_, v_a_920_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_932_, lean_object* v_a_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_932_, v_a_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
return v_res_944_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_31792__overap_958_; lean_object* v___x_959_; 
v___x_957_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
v___x_31792__overap_958_ = lean_panic_fn_borrowed(v___x_957_, v_msg_946_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
v___x_959_ = lean_apply_10(v___x_31792__overap_958_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
return v_res_971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_977_ = l_Lean_Expr_const___override(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_980_ = lean_unsigned_to_nat(52u);
v___x_981_ = lean_unsigned_to_nat(265u);
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_984_ = l_mkPanicMessageWithDecl(v___x_983_, v___x_982_, v___x_981_, v___x_980_, v___x_979_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_986_ = lean_unsigned_to_nat(52u);
v___x_987_ = lean_unsigned_to_nat(257u);
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_990_ = l_mkPanicMessageWithDecl(v___x_989_, v___x_988_, v___x_987_, v___x_986_, v___x_985_);
return v___x_990_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_992_ = lean_unsigned_to_nat(52u);
v___x_993_ = lean_unsigned_to_nat(272u);
v___x_994_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_996_ = l_mkPanicMessageWithDecl(v___x_995_, v___x_994_, v___x_993_, v___x_992_, v___x_991_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_998_ = lean_unsigned_to_nat(26u);
v___x_999_ = lean_unsigned_to_nat(250u);
v___x_1000_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1002_ = l_mkPanicMessageWithDecl(v___x_1001_, v___x_1000_, v___x_999_, v___x_998_, v___x_997_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1006_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1008_, lean_object* v_e_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_nat_dec_eq(v_i_1008_, v___x_1020_);
if (v___x_1021_ == 0)
{
if (lean_obj_tag(v_e_1009_) == 5)
{
lean_object* v_fn_1022_; lean_object* v_arg_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_fn_1022_ = lean_ctor_get(v_e_1009_, 0);
lean_inc_ref_n(v_fn_1022_, 2);
v_arg_1023_ = lean_ctor_get(v_e_1009_, 1);
lean_inc_ref(v_arg_1023_);
lean_dec_ref_known(v_e_1009_, 2);
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_nat_sub(v_i_1008_, v___x_1024_);
v___x_1026_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1025_, v_fn_1022_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1285_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v_fst_1028_ = lean_ctor_get(v_a_1027_, 0);
v_snd_1029_ = lean_ctor_get(v_a_1027_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1031_ = v_a_1027_;
v_isShared_1032_ = v_isSharedCheck_1285_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_snd_1029_);
lean_inc(v_fst_1028_);
lean_dec(v_a_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1285_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; 
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_a_1014_);
lean_inc_ref(v_a_1013_);
lean_inc(v_a_1012_);
lean_inc_ref(v_a_1011_);
lean_inc(v_a_1010_);
lean_inc_ref(v_arg_1023_);
v___x_1033_ = lean_sym_simp(v_arg_1023_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1276_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1276_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1276_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___y_1039_; uint8_t v___x_1048_; 
v___x_1048_ = 1;
if (lean_obj_tag(v_fst_1028_) == 0)
{
lean_dec(v_snd_1029_);
if (lean_obj_tag(v_a_1034_) == 0)
{
uint8_t v_contextDependent_1049_; 
lean_dec(v___x_1025_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_contextDependent_1049_ = lean_ctor_get_uint8(v_fst_1028_, 1);
lean_dec_ref_known(v_fst_1028_, 0);
if (v_contextDependent_1049_ == 0)
{
uint8_t v_contextDependent_1050_; 
v_contextDependent_1050_ = lean_ctor_get_uint8(v_a_1034_, 1);
lean_dec_ref_known(v_a_1034_, 0);
v___y_1039_ = v_contextDependent_1050_;
goto v___jp_1038_;
}
else
{
lean_dec_ref_known(v_a_1034_, 0);
v___y_1039_ = v___x_1048_;
goto v___jp_1038_;
}
}
else
{
uint8_t v_contextDependent_1051_; lean_object* v_e_x27_1052_; lean_object* v_proof_1053_; uint8_t v_contextDependent_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1131_; 
lean_del_object(v___x_1036_);
lean_del_object(v___x_1031_);
v_contextDependent_1051_ = lean_ctor_get_uint8(v_fst_1028_, 1);
lean_dec_ref_known(v_fst_1028_, 0);
v_e_x27_1052_ = lean_ctor_get(v_a_1034_, 0);
v_proof_1053_ = lean_ctor_get(v_a_1034_, 1);
v_contextDependent_1054_ = lean_ctor_get_uint8(v_a_1034_, sizeof(void*)*2 + 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1056_ = v_a_1034_;
v_isShared_1057_ = v_isSharedCheck_1131_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_proof_1053_);
lean_inc(v_e_x27_1052_);
lean_dec(v_a_1034_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1131_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; 
lean_inc_ref(v_fn_1022_);
v___x_1058_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1022_, v___x_1025_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v___x_1025_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_1059_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
if (lean_obj_tag(v_a_1061_) == 7)
{
lean_object* v_binderType_1062_; lean_object* v_body_1063_; lean_object* v___x_1064_; 
v_binderType_1062_ = lean_ctor_get(v_a_1061_, 1);
lean_inc_ref(v_binderType_1062_);
v_body_1063_ = lean_ctor_get(v_a_1061_, 2);
lean_inc_ref(v_body_1063_);
lean_dec_ref_known(v_a_1061_, 3);
lean_inc_ref(v_e_x27_1052_);
lean_inc_ref(v_fn_1022_);
v___x_1064_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1022_, v_e_x27_1052_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
lean_inc_ref(v_binderType_1062_);
v___x_1066_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1062_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
lean_inc_ref(v_body_1063_);
v___x_1068_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1063_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1088_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1088_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1088_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___y_1080_; 
v___x_1073_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1069_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1067_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_mkConst(v___x_1073_, v___x_1076_);
lean_inc_ref(v_body_1063_);
v___x_1078_ = l_Lean_mkApp6(v___x_1077_, v_binderType_1062_, v_body_1063_, v_arg_1023_, v_e_x27_1052_, v_fn_1022_, v_proof_1053_);
if (v_contextDependent_1051_ == 0)
{
v___y_1080_ = v_contextDependent_1054_;
goto v___jp_1079_;
}
else
{
v___y_1080_ = v___x_1048_;
goto v___jp_1079_;
}
v___jp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1078_);
lean_ctor_set(v___x_1056_, 0, v_a_1065_);
v___x_1082_ = v___x_1056_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1065_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1078_);
v___x_1082_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*2, v___x_1021_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*2 + 1, v___y_1080_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_body_1063_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1083_);
v___x_1085_ = v___x_1071_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_1067_);
lean_dec(v_a_1065_);
lean_dec_ref(v_body_1063_);
lean_dec_ref(v_binderType_1062_);
lean_del_object(v___x_1056_);
lean_dec_ref(v_proof_1053_);
lean_dec_ref(v_e_x27_1052_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1089_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1068_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1068_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_a_1065_);
lean_dec_ref(v_body_1063_);
lean_dec_ref(v_binderType_1062_);
lean_del_object(v___x_1056_);
lean_dec_ref(v_proof_1053_);
lean_dec_ref(v_e_x27_1052_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1097_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1066_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1066_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_body_1063_);
lean_dec_ref(v_binderType_1062_);
lean_del_object(v___x_1056_);
lean_dec_ref(v_proof_1053_);
lean_dec_ref(v_e_x27_1052_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1105_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1064_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1064_);
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
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_a_1061_);
lean_del_object(v___x_1056_);
lean_dec_ref(v_proof_1053_);
lean_dec_ref(v_e_x27_1052_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v___x_1113_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1114_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1113_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1114_;
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_del_object(v___x_1056_);
lean_dec_ref(v_proof_1053_);
lean_dec_ref(v_e_x27_1052_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1115_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1060_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1060_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_del_object(v___x_1056_);
lean_dec_ref(v_proof_1053_);
lean_dec_ref(v_e_x27_1052_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1123_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1058_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1058_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1036_);
lean_del_object(v___x_1031_);
lean_dec(v___x_1025_);
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_object* v_e_x27_1132_; lean_object* v_proof_1133_; uint8_t v_contextDependent_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1202_; 
v_e_x27_1132_ = lean_ctor_get(v_fst_1028_, 0);
v_proof_1133_ = lean_ctor_get(v_fst_1028_, 1);
v_contextDependent_1134_ = lean_ctor_get_uint8(v_fst_1028_, sizeof(void*)*2 + 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_fst_1028_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1136_ = v_fst_1028_;
v_isShared_1137_ = v_isSharedCheck_1202_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_proof_1133_);
lean_inc(v_e_x27_1132_);
lean_dec(v_fst_1028_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1202_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
uint8_t v_contextDependent_1138_; lean_object* v___x_1139_; 
v_contextDependent_1138_ = lean_ctor_get_uint8(v_a_1034_, 1);
lean_dec_ref_known(v_a_1034_, 0);
v___x_1139_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1029_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
if (lean_obj_tag(v_a_1140_) == 7)
{
lean_object* v_binderType_1141_; lean_object* v_body_1142_; lean_object* v___x_1143_; 
v_binderType_1141_ = lean_ctor_get(v_a_1140_, 1);
lean_inc_ref(v_binderType_1141_);
v_body_1142_ = lean_ctor_get(v_a_1140_, 2);
lean_inc_ref(v_body_1142_);
lean_dec_ref_known(v_a_1140_, 3);
lean_inc_ref(v_arg_1023_);
lean_inc_ref(v_e_x27_1132_);
v___x_1143_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1132_, v_arg_1023_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
lean_inc_ref(v_binderType_1141_);
v___x_1145_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1141_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
lean_inc_ref(v_body_1142_);
v___x_1147_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1142_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1167_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1167_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1167_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___y_1159_; 
v___x_1152_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1148_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1146_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_mkConst(v___x_1152_, v___x_1155_);
lean_inc_ref(v_body_1142_);
v___x_1157_ = l_Lean_mkApp6(v___x_1156_, v_binderType_1141_, v_body_1142_, v_fn_1022_, v_e_x27_1132_, v_proof_1133_, v_arg_1023_);
if (v_contextDependent_1134_ == 0)
{
v___y_1159_ = v_contextDependent_1138_;
goto v___jp_1158_;
}
else
{
v___y_1159_ = v___x_1048_;
goto v___jp_1158_;
}
v___jp_1158_:
{
lean_object* v___x_1161_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1157_);
lean_ctor_set(v___x_1136_, 0, v_a_1144_);
v___x_1161_ = v___x_1136_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1144_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1157_);
v___x_1161_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*2, v___x_1021_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*2 + 1, v___y_1159_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_body_1142_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1162_);
v___x_1164_ = v___x_1150_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_a_1146_);
lean_dec(v_a_1144_);
lean_dec_ref(v_body_1142_);
lean_dec_ref(v_binderType_1141_);
lean_del_object(v___x_1136_);
lean_dec_ref(v_proof_1133_);
lean_dec_ref(v_e_x27_1132_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1168_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1147_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1147_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_a_1144_);
lean_dec_ref(v_body_1142_);
lean_dec_ref(v_binderType_1141_);
lean_del_object(v___x_1136_);
lean_dec_ref(v_proof_1133_);
lean_dec_ref(v_e_x27_1132_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1176_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1145_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1145_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_body_1142_);
lean_dec_ref(v_binderType_1141_);
lean_del_object(v___x_1136_);
lean_dec_ref(v_proof_1133_);
lean_dec_ref(v_e_x27_1132_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1184_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1143_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1143_);
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
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec(v_a_1140_);
lean_del_object(v___x_1136_);
lean_dec_ref(v_proof_1133_);
lean_dec_ref(v_e_x27_1132_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v___x_1192_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1193_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1192_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1193_;
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_del_object(v___x_1136_);
lean_dec_ref(v_proof_1133_);
lean_dec_ref(v_e_x27_1132_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1194_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1139_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1139_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1203_; lean_object* v_proof_1204_; uint8_t v_contextDependent_1205_; lean_object* v_e_x27_1206_; lean_object* v_proof_1207_; uint8_t v_contextDependent_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1275_; 
v_e_x27_1203_ = lean_ctor_get(v_fst_1028_, 0);
lean_inc_ref(v_e_x27_1203_);
v_proof_1204_ = lean_ctor_get(v_fst_1028_, 1);
lean_inc_ref(v_proof_1204_);
v_contextDependent_1205_ = lean_ctor_get_uint8(v_fst_1028_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1028_, 2);
v_e_x27_1206_ = lean_ctor_get(v_a_1034_, 0);
v_proof_1207_ = lean_ctor_get(v_a_1034_, 1);
v_contextDependent_1208_ = lean_ctor_get_uint8(v_a_1034_, sizeof(void*)*2 + 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1210_ = v_a_1034_;
v_isShared_1211_ = v_isSharedCheck_1275_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_proof_1207_);
lean_inc(v_e_x27_1206_);
lean_dec(v_a_1034_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1275_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1029_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
if (lean_obj_tag(v_a_1213_) == 7)
{
lean_object* v_binderType_1214_; lean_object* v_body_1215_; lean_object* v___x_1216_; 
v_binderType_1214_ = lean_ctor_get(v_a_1213_, 1);
lean_inc_ref(v_binderType_1214_);
v_body_1215_ = lean_ctor_get(v_a_1213_, 2);
lean_inc_ref(v_body_1215_);
lean_dec_ref_known(v_a_1213_, 3);
lean_inc_ref(v_e_x27_1206_);
lean_inc_ref(v_e_x27_1203_);
v___x_1216_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1203_, v_e_x27_1206_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
lean_inc_ref(v_binderType_1214_);
v___x_1218_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1214_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
lean_inc_ref(v_body_1215_);
v___x_1220_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1215_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1240_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1240_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1240_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___y_1232_; 
v___x_1225_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1221_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1219_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_mkConst(v___x_1225_, v___x_1228_);
lean_inc_ref(v_body_1215_);
v___x_1230_ = l_Lean_mkApp8(v___x_1229_, v_binderType_1214_, v_body_1215_, v_fn_1022_, v_e_x27_1203_, v_arg_1023_, v_e_x27_1206_, v_proof_1204_, v_proof_1207_);
if (v_contextDependent_1205_ == 0)
{
v___y_1232_ = v_contextDependent_1208_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v___x_1048_;
goto v___jp_1231_;
}
v___jp_1231_:
{
lean_object* v___x_1234_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1230_);
lean_ctor_set(v___x_1210_, 0, v_a_1217_);
v___x_1234_ = v___x_1210_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1217_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1230_);
v___x_1234_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*2, v___x_1021_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*2 + 1, v___y_1232_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_body_1215_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1235_);
v___x_1237_ = v___x_1223_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
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
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_a_1219_);
lean_dec(v_a_1217_);
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_del_object(v___x_1210_);
lean_dec_ref(v_proof_1207_);
lean_dec_ref(v_e_x27_1206_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1241_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1220_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1220_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1217_);
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_del_object(v___x_1210_);
lean_dec_ref(v_proof_1207_);
lean_dec_ref(v_e_x27_1206_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1249_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1218_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1218_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_del_object(v___x_1210_);
lean_dec_ref(v_proof_1207_);
lean_dec_ref(v_e_x27_1206_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1257_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1216_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1216_);
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
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_a_1213_);
lean_del_object(v___x_1210_);
lean_dec_ref(v_proof_1207_);
lean_dec_ref(v_e_x27_1206_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v___x_1265_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1266_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1265_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1266_;
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_del_object(v___x_1210_);
lean_dec_ref(v_proof_1207_);
lean_dec_ref(v_e_x27_1206_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1267_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1212_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1212_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1040_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1039_);
v___x_1041_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1041_);
lean_ctor_set(v___x_1031_, 0, v___x_1040_);
v___x_1043_ = v___x_1031_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1043_);
v___x_1045_ = v___x_1036_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_del_object(v___x_1031_);
lean_dec(v_snd_1029_);
lean_dec(v_fst_1028_);
lean_dec(v___x_1025_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
v_a_1277_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1033_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1033_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_dec(v___x_1025_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_fn_1022_);
return v___x_1026_;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref(v_e_1009_);
v___x_1286_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1287_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1286_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v_e_1009_);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1290_, lean_object* v_e_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1290_, v_e_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec(v_i_1290_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1303_, lean_object* v_e_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1303_, v_e_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_fst_1320_; lean_object* v___x_1322_; 
v_fst_1320_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_fst_1320_);
lean_dec(v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_fst_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_fst_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1315_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1315_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1333_, lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1333_, v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec(v_n_1333_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1346_, lean_object* v_prefixSize_1347_, lean_object* v_suffixSize_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_numArgs_1359_; uint8_t v___x_1360_; 
v_numArgs_1359_ = l_Lean_Expr_getAppNumArgs(v_e_1346_);
v___x_1360_ = lean_nat_dec_le(v_numArgs_1359_, v_prefixSize_1347_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = lean_nat_add(v_prefixSize_1347_, v_suffixSize_1348_);
v___x_1362_ = lean_nat_dec_lt(v___x_1361_, v_numArgs_1359_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v_suffixSize_1348_);
v___x_1363_ = lean_nat_sub(v_numArgs_1359_, v_prefixSize_1347_);
lean_dec(v_numArgs_1359_);
v___x_1364_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1363_, v_e_1346_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
lean_dec(v___x_1363_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1365_ = lean_nat_sub(v_numArgs_1359_, v_prefixSize_1347_);
lean_dec(v_numArgs_1359_);
v___x_1366_ = lean_nat_sub(v___x_1365_, v_suffixSize_1348_);
lean_dec(v___x_1365_);
v___x_1367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1367_, 0, v_suffixSize_1348_);
v___x_1368_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1367_, v_e_1346_, v___x_1366_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
lean_dec(v___x_1366_);
return v___x_1368_;
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v_numArgs_1359_);
lean_dec(v_suffixSize_1348_);
lean_dec_ref(v_e_1346_);
v___x_1369_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1371_, lean_object* v_prefixSize_1372_, lean_object* v_suffixSize_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1371_, v_prefixSize_1372_, v_suffixSize_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec(v_prefixSize_1372_);
return v_res_1384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1387_ = lean_unsigned_to_nat(13u);
v___x_1388_ = lean_unsigned_to_nat(308u);
v___x_1389_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1390_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1391_ = l_mkPanicMessageWithDecl(v___x_1390_, v___x_1389_, v___x_1388_, v___x_1387_, v___x_1386_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1392_, lean_object* v_i_1393_, lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_nat_dec_eq(v_i_1393_, v___x_1405_);
if (v___x_1406_ == 0)
{
if (lean_obj_tag(v_e_1394_) == 5)
{
lean_object* v_fn_1407_; lean_object* v_arg_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_fn_1407_ = lean_ctor_get(v_e_1394_, 0);
lean_inc_ref_n(v_fn_1407_, 2);
v_arg_1408_ = lean_ctor_get(v_e_1394_, 1);
lean_inc_ref(v_arg_1408_);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_sub(v_i_1393_, v___x_1409_);
v___x_1411_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1392_, v___x_1410_, v_fn_1407_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1431_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1431_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1431_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = lean_array_fget_borrowed(v_rewritable_1392_, v___x_1410_);
lean_dec(v___x_1410_);
v___x_1417_ = lean_unbox(v___x_1416_);
if (v___x_1417_ == 0)
{
if (lean_obj_tag(v_a_1412_) == 0)
{
uint8_t v_contextDependent_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_dec_ref(v_arg_1408_);
lean_dec_ref_known(v_e_1394_, 2);
lean_dec_ref(v_fn_1407_);
v_contextDependent_1418_ = lean_ctor_get_uint8(v_a_1412_, 1);
lean_dec_ref_known(v_a_1412_, 0);
v___x_1419_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1418_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1419_);
v___x_1421_ = v___x_1414_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
else
{
lean_object* v_e_x27_1423_; lean_object* v_proof_1424_; uint8_t v_contextDependent_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
lean_del_object(v___x_1414_);
v_e_x27_1423_ = lean_ctor_get(v_a_1412_, 0);
lean_inc_ref(v_e_x27_1423_);
v_proof_1424_ = lean_ctor_get(v_a_1412_, 1);
lean_inc_ref(v_proof_1424_);
v_contextDependent_1425_ = lean_ctor_get_uint8(v_a_1412_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1412_, 2);
v___x_1426_ = lean_unbox(v___x_1416_);
v___x_1427_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1394_, v_fn_1407_, v_arg_1408_, v_e_x27_1423_, v_proof_1424_, v___x_1426_, v_contextDependent_1425_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
return v___x_1427_;
}
}
else
{
lean_object* v___x_1428_; 
lean_del_object(v___x_1414_);
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
lean_inc(v_a_1401_);
lean_inc_ref(v_a_1400_);
lean_inc(v_a_1399_);
lean_inc_ref(v_a_1398_);
lean_inc(v_a_1397_);
lean_inc_ref(v_a_1396_);
lean_inc(v_a_1395_);
lean_inc_ref(v_arg_1408_);
v___x_1428_ = lean_sym_simp(v_arg_1408_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1394_, v_fn_1407_, v_arg_1408_, v_a_1412_, v_a_1429_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
return v___x_1430_;
}
else
{
lean_dec(v_a_1412_);
lean_dec_ref(v_arg_1408_);
lean_dec_ref_known(v_e_1394_, 2);
lean_dec_ref(v_fn_1407_);
return v___x_1428_;
}
}
}
}
else
{
lean_dec(v___x_1410_);
lean_dec_ref(v_arg_1408_);
lean_dec_ref_known(v_e_1394_, 2);
lean_dec_ref(v_fn_1407_);
return v___x_1411_;
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_e_1394_);
v___x_1432_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1433_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1432_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
return v___x_1433_;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_e_1394_);
v___x_1434_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1436_, lean_object* v_i_1437_, lean_object* v_e_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1436_, v_i_1437_, v_e_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_i_1437_);
lean_dec_ref(v_rewritable_1436_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1450_, lean_object* v_i_1451_, lean_object* v_e_1452_, lean_object* v_h_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1450_, v_i_1451_, v_e_1452_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1465_, lean_object* v_i_1466_, lean_object* v_e_1467_, lean_object* v_h_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1465_, v_i_1466_, v_e_1467_, v_h_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec(v_i_1466_);
lean_dec_ref(v_rewritable_1465_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1480_, lean_object* v___x_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1480_, v___x_1481_, v_x_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1494_, lean_object* v___x_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1494_, v___x_1495_, v_x_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v___x_1495_);
lean_dec_ref(v_rewritable_1494_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1508_, lean_object* v_rewritable_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_numArgs_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_numArgs_1520_ = l_Lean_Expr_getAppNumArgs(v_e_1508_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_nat_dec_eq(v_numArgs_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = lean_array_get_size(v_rewritable_1509_);
v___x_1524_ = lean_nat_dec_lt(v___x_1523_, v_numArgs_1520_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1509_, v_numArgs_1520_, v_e_1508_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_numArgs_1520_);
lean_dec_ref(v_rewritable_1509_);
return v___x_1525_;
}
else
{
lean_object* v___f_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___f_1526_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1526_, 0, v_rewritable_1509_);
lean_closure_set(v___f_1526_, 1, v___x_1523_);
v___x_1527_ = lean_nat_sub(v_numArgs_1520_, v___x_1523_);
lean_dec(v_numArgs_1520_);
v___x_1528_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1526_, v_e_1508_, v___x_1527_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v___x_1527_);
return v___x_1528_;
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_numArgs_1520_);
lean_dec_ref(v_rewritable_1509_);
lean_dec_ref(v_e_1508_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1531_, lean_object* v_rewritable_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1531_, v_rewritable_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1544_, lean_object* v_numEqs_1545_, lean_object* v_result_1546_){
_start:
{
if (lean_obj_tag(v_result_1546_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
lean_dec(v_numEqs_1545_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_array_get_size(v_argResults_1544_);
v___x_1549_ = lean_nat_dec_lt(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_dec_ref_known(v_result_1546_, 0);
return v_argResults_1544_;
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_array_push(v_argResults_1544_, v_result_1546_);
return v___x_1550_;
}
}
else
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_array_get_size(v_argResults_1544_);
v___x_1552_ = lean_nat_dec_lt(v___x_1551_, v_numEqs_1545_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec(v_numEqs_1545_);
v___x_1553_ = lean_array_push(v_argResults_1544_, v_result_1546_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref(v_argResults_1544_);
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1555_ = lean_mk_array(v_numEqs_1545_, v___x_1554_);
v___x_1556_ = lean_array_push(v___x_1555_, v_result_1546_);
return v___x_1556_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1559_ = lean_unsigned_to_nat(13u);
v___x_1560_ = lean_unsigned_to_nat(429u);
v___x_1561_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1562_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1563_ = l_mkPanicMessageWithDecl(v___x_1562_, v___x_1561_, v___x_1560_, v___x_1559_, v___x_1558_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1564_, lean_object* v_mkNonRflResult_1565_, lean_object* v_e_1566_, lean_object* v_i_1567_, lean_object* v_numEqs_1568_, lean_object* v_argResults_1569_, uint8_t v_anyCD_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
if (lean_obj_tag(v_e_1566_) == 5)
{
lean_object* v_fn_1581_; lean_object* v_arg_1582_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v_fn_1581_ = lean_ctor_get(v_e_1566_, 0);
lean_inc_ref(v_fn_1581_);
v_arg_1582_ = lean_ctor_get(v_e_1566_, 1);
lean_inc_ref(v_arg_1582_);
lean_dec_ref_known(v_e_1566_, 2);
v___x_1596_ = 0;
v___x_1597_ = lean_box(v___x_1596_);
v___x_1598_ = lean_array_get(v___x_1597_, v_argKinds_1564_, v_i_1567_);
lean_dec(v___x_1597_);
v___x_1599_ = lean_unbox(v___x_1598_);
lean_dec(v___x_1598_);
switch(v___x_1599_)
{
case 5:
{
lean_dec_ref(v_arg_1582_);
v___y_1584_ = v_a_1571_;
v___y_1585_ = v_a_1572_;
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
goto v___jp_1583_;
}
case 0:
{
lean_dec_ref(v_arg_1582_);
v___y_1584_ = v_a_1571_;
v___y_1585_ = v_a_1572_;
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
goto v___jp_1583_;
}
case 3:
{
lean_dec_ref(v_arg_1582_);
v___y_1584_ = v_a_1571_;
v___y_1585_ = v_a_1572_;
v___y_1586_ = v_a_1573_;
v___y_1587_ = v_a_1574_;
v___y_1588_ = v_a_1575_;
v___y_1589_ = v_a_1576_;
v___y_1590_ = v_a_1577_;
v___y_1591_ = v_a_1578_;
v___y_1592_ = v_a_1579_;
goto v___jp_1583_;
}
case 2:
{
lean_object* v___x_1600_; 
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc_ref(v_a_1574_);
lean_inc(v_a_1573_);
lean_inc_ref(v_a_1572_);
lean_inc(v_a_1571_);
v___x_1600_ = lean_sym_simp(v_arg_1582_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_n(v_a_1601_, 2);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_sub(v_i_1567_, v___x_1602_);
lean_dec(v_i_1567_);
v___x_1604_ = lean_nat_add(v_numEqs_1568_, v___x_1602_);
v___x_1605_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1569_, v_numEqs_1568_, v_a_1601_);
if (v_anyCD_1570_ == 0)
{
if (lean_obj_tag(v_a_1601_) == 0)
{
uint8_t v_contextDependent_1606_; 
v_contextDependent_1606_ = lean_ctor_get_uint8(v_a_1601_, 1);
lean_dec_ref_known(v_a_1601_, 0);
v_e_1566_ = v_fn_1581_;
v_i_1567_ = v___x_1603_;
v_numEqs_1568_ = v___x_1604_;
v_argResults_1569_ = v___x_1605_;
v_anyCD_1570_ = v_contextDependent_1606_;
goto _start;
}
else
{
uint8_t v_contextDependent_1608_; 
v_contextDependent_1608_ = lean_ctor_get_uint8(v_a_1601_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1601_, 2);
v_e_1566_ = v_fn_1581_;
v_i_1567_ = v___x_1603_;
v_numEqs_1568_ = v___x_1604_;
v_argResults_1569_ = v___x_1605_;
v_anyCD_1570_ = v_contextDependent_1608_;
goto _start;
}
}
else
{
lean_dec(v_a_1601_);
v_e_1566_ = v_fn_1581_;
v_i_1567_ = v___x_1603_;
v_numEqs_1568_ = v___x_1604_;
v_argResults_1569_ = v___x_1605_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_1581_);
lean_dec_ref(v_argResults_1569_);
lean_dec(v_numEqs_1568_);
lean_dec(v_i_1567_);
lean_dec_ref(v_mkNonRflResult_1565_);
return v___x_1600_;
}
}
default: 
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v_arg_1582_);
lean_dec_ref(v_fn_1581_);
lean_dec_ref(v_argResults_1569_);
lean_dec(v_numEqs_1568_);
lean_dec(v_i_1567_);
lean_dec_ref(v_mkNonRflResult_1565_);
v___x_1611_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1612_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1611_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1612_;
}
}
v___jp_1583_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_sub(v_i_1567_, v___x_1593_);
lean_dec(v_i_1567_);
v_e_1566_ = v_fn_1581_;
v_i_1567_ = v___x_1594_;
v_a_1571_ = v___y_1584_;
v_a_1572_ = v___y_1585_;
v_a_1573_ = v___y_1586_;
v_a_1574_ = v___y_1587_;
v_a_1575_ = v___y_1588_;
v_a_1576_ = v___y_1589_;
v_a_1577_ = v___y_1590_;
v_a_1578_ = v___y_1591_;
v_a_1579_ = v___y_1592_;
goto _start;
}
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
lean_dec(v_numEqs_1568_);
lean_dec(v_i_1567_);
lean_dec_ref(v_e_1566_);
v___x_1613_ = lean_array_get_size(v_argResults_1569_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_nat_dec_eq(v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l_Array_reverse___redArg(v_argResults_1569_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc_ref(v_a_1574_);
lean_inc(v_a_1573_);
lean_inc_ref(v_a_1572_);
lean_inc(v_a_1571_);
v___x_1617_ = lean_apply_11(v_mkNonRflResult_1565_, v___x_1616_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___y_1623_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
if (v_anyCD_1570_ == 0)
{
lean_dec(v_a_1618_);
return v___x_1617_;
}
else
{
if (lean_obj_tag(v_a_1618_) == 0)
{
uint8_t v_contextDependent_1624_; 
v_contextDependent_1624_ = lean_ctor_get_uint8(v_a_1618_, 1);
v___y_1623_ = v_contextDependent_1624_;
goto v___jp_1622_;
}
else
{
uint8_t v_contextDependent_1625_; 
v_contextDependent_1625_ = lean_ctor_get_uint8(v_a_1618_, sizeof(void*)*2 + 1);
v___y_1623_ = v_contextDependent_1625_;
goto v___jp_1622_;
}
}
v___jp_1619_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1618_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
v___jp_1622_:
{
if (v___y_1623_ == 0)
{
lean_dec_ref_known(v___x_1617_, 1);
goto v___jp_1619_;
}
else
{
if (v___x_1615_ == 0)
{
lean_dec(v_a_1618_);
return v___x_1617_;
}
else
{
lean_dec_ref_known(v___x_1617_, 1);
goto v___jp_1619_;
}
}
}
}
else
{
return v___x_1617_;
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v_argResults_1569_);
lean_dec_ref(v_mkNonRflResult_1565_);
v___x_1626_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_1570_);
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
lean_object* v___x_1659_; lean_object* v___x_21488__overap_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
v___x_21488__overap_1660_ = lean_panic_fn_borrowed(v___x_1659_, v_msg_1648_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1649_);
v___x_1661_ = lean_apply_10(v___x_21488__overap_1660_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, lean_box(0));
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
uint8_t v___x_1678_; 
v___x_1678_ = lean_usize_dec_eq(v_i_1676_, v_stop_1677_);
if (v___x_1678_ == 0)
{
uint8_t v___x_1679_; uint8_t v___y_1681_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1679_ = 1;
v___x_1685_ = lean_array_uget_borrowed(v_as_1675_, v_i_1676_);
v___x_1686_ = lean_unbox(v___x_1685_);
if (v___x_1686_ == 3)
{
v___y_1681_ = v___x_1674_;
goto v___jp_1680_;
}
else
{
v___y_1681_ = v___x_1678_;
goto v___jp_1680_;
}
v___jp_1680_:
{
if (v___y_1681_ == 0)
{
size_t v___x_1682_; size_t v___x_1683_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1676_, v___x_1682_);
v_i_1676_ = v___x_1683_;
goto _start;
}
else
{
return v___x_1679_;
}
}
}
else
{
uint8_t v___x_1687_; 
v___x_1687_ = 0;
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object* v___x_1688_, lean_object* v_as_1689_, lean_object* v_i_1690_, lean_object* v_stop_1691_){
_start:
{
uint8_t v___x_23302__boxed_1692_; size_t v_i_boxed_1693_; size_t v_stop_boxed_1694_; uint8_t v_res_1695_; lean_object* v_r_1696_; 
v___x_23302__boxed_1692_ = lean_unbox(v___x_1688_);
v_i_boxed_1693_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_stop_boxed_1694_ = lean_unbox_usize(v_stop_1691_);
lean_dec(v_stop_1691_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_23302__boxed_1692_, v_as_1689_, v_i_boxed_1693_, v_stop_boxed_1694_);
lean_dec_ref(v_as_1689_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object* v_as_1697_, size_t v_i_1698_, size_t v_stop_1699_){
_start:
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_usize_dec_eq(v_i_1698_, v_stop_1699_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; uint8_t v___y_1703_; lean_object* v___x_1707_; 
v___x_1701_ = 1;
v___x_1707_ = lean_array_uget_borrowed(v_as_1697_, v_i_1698_);
if (lean_obj_tag(v___x_1707_) == 0)
{
uint8_t v_contextDependent_1708_; 
v_contextDependent_1708_ = lean_ctor_get_uint8(v___x_1707_, 1);
v___y_1703_ = v_contextDependent_1708_;
goto v___jp_1702_;
}
else
{
uint8_t v_contextDependent_1709_; 
v_contextDependent_1709_ = lean_ctor_get_uint8(v___x_1707_, sizeof(void*)*2 + 1);
v___y_1703_ = v_contextDependent_1709_;
goto v___jp_1702_;
}
v___jp_1702_:
{
if (v___y_1703_ == 0)
{
size_t v___x_1704_; size_t v___x_1705_; 
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1698_, v___x_1704_);
v_i_1698_ = v___x_1705_;
goto _start;
}
else
{
return v___x_1701_;
}
}
}
else
{
uint8_t v___x_1710_; 
v___x_1710_ = 0;
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v_as_1711_, lean_object* v_i_1712_, lean_object* v_stop_1713_){
_start:
{
size_t v_i_boxed_1714_; size_t v_stop_boxed_1715_; uint8_t v_res_1716_; lean_object* v_r_1717_; 
v_i_boxed_1714_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_stop_boxed_1715_ = lean_unbox_usize(v_stop_1713_);
lean_dec(v_stop_1713_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1711_, v_i_boxed_1714_, v_stop_boxed_1715_);
lean_dec_ref(v_as_1711_);
v_r_1717_ = lean_box(v_res_1716_);
return v_r_1717_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1720_ = lean_unsigned_to_nat(13u);
v___x_1721_ = lean_unsigned_to_nat(401u);
v___x_1722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1724_ = l_mkPanicMessageWithDecl(v___x_1723_, v___x_1722_, v___x_1721_, v___x_1720_, v___x_1719_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1725_, lean_object* v_as_1726_, size_t v_sz_1727_, size_t v_i_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_a_1741_; uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_lt(v_i_1728_, v_sz_1727_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1729_);
return v___x_1746_;
}
else
{
lean_object* v_snd_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1942_; 
v_snd_1747_ = lean_ctor_get(v_b_1729_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_b_1729_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_b_1729_, 0);
lean_dec(v_unused_1943_);
v___x_1749_ = v_b_1729_;
v_isShared_1750_ = v_isSharedCheck_1942_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_snd_1747_);
lean_dec(v_b_1729_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1942_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_snd_1751_; lean_object* v_snd_1752_; lean_object* v_snd_1753_; lean_object* v_snd_1754_; lean_object* v_fst_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1940_; 
v_snd_1751_ = lean_ctor_get(v_snd_1747_, 1);
lean_inc(v_snd_1751_);
v_snd_1752_ = lean_ctor_get(v_snd_1751_, 1);
lean_inc(v_snd_1752_);
v_snd_1753_ = lean_ctor_get(v_snd_1752_, 1);
lean_inc(v_snd_1753_);
v_snd_1754_ = lean_ctor_get(v_snd_1753_, 1);
lean_inc(v_snd_1754_);
v_fst_1755_ = lean_ctor_get(v_snd_1747_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_snd_1747_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_snd_1747_, 1);
lean_dec(v_unused_1941_);
v___x_1757_ = v_snd_1747_;
v_isShared_1758_ = v_isSharedCheck_1940_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_fst_1755_);
lean_dec(v_snd_1747_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1940_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_fst_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1938_; 
v_fst_1759_ = lean_ctor_get(v_snd_1751_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_snd_1751_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_snd_1751_, 1);
lean_dec(v_unused_1939_);
v___x_1761_ = v_snd_1751_;
v_isShared_1762_ = v_isSharedCheck_1938_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_fst_1759_);
lean_dec(v_snd_1751_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1938_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_fst_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1936_; 
v_fst_1763_ = lean_ctor_get(v_snd_1752_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_snd_1752_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_snd_1752_, 1);
lean_dec(v_unused_1937_);
v___x_1765_ = v_snd_1752_;
v_isShared_1766_ = v_isSharedCheck_1936_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_fst_1763_);
lean_dec(v_snd_1752_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1936_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_fst_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1934_; 
v_fst_1767_ = lean_ctor_get(v_snd_1753_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_snd_1753_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_snd_1753_, 1);
lean_dec(v_unused_1935_);
v___x_1769_ = v_snd_1753_;
v_isShared_1770_ = v_isSharedCheck_1934_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_fst_1767_);
lean_dec(v_snd_1753_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1934_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_array_1771_; lean_object* v_start_1772_; lean_object* v_stop_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_array_1771_ = lean_ctor_get(v_snd_1754_, 0);
v_start_1772_ = lean_ctor_get(v_snd_1754_, 1);
v_stop_1773_ = lean_ctor_get(v_snd_1754_, 2);
v___x_1774_ = lean_box(0);
v___x_1775_ = lean_nat_dec_lt(v_start_1772_, v_stop_1773_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1777_; 
if (v_isShared_1770_ == 0)
{
v___x_1777_ = v___x_1769_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_fst_1767_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_snd_1754_);
v___x_1777_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1777_);
v___x_1779_ = v___x_1765_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_fst_1763_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1779_);
v___x_1781_ = v___x_1761_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_fst_1759_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1781_);
v___x_1783_ = v___x_1757_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_fst_1755_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1783_);
lean_ctor_set(v___x_1749_, 0, v___x_1774_);
v___x_1785_ = v___x_1749_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
}
}
}
}
}
else
{
lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1930_; 
lean_inc(v_stop_1773_);
lean_inc(v_start_1772_);
lean_inc_ref(v_array_1771_);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_snd_1754_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; lean_object* v_unused_1932_; lean_object* v_unused_1933_; 
v_unused_1931_ = lean_ctor_get(v_snd_1754_, 2);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_snd_1754_, 1);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_snd_1754_, 0);
lean_dec(v_unused_1933_);
v___x_1793_ = v_snd_1754_;
v_isShared_1794_ = v_isSharedCheck_1930_;
goto v_resetjp_1792_;
}
else
{
lean_dec(v_snd_1754_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1930_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v_a_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v_a_1795_ = lean_array_uget_borrowed(v_as_1726_, v_i_1728_);
v___x_1796_ = lean_array_fget(v_array_1771_, v_start_1772_);
v___x_1797_ = lean_unsigned_to_nat(1u);
v___x_1798_ = lean_nat_add(v_start_1772_, v___x_1797_);
lean_dec(v_start_1772_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1798_);
v___x_1800_ = v___x_1793_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_array_1771_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_stop_1773_);
v___x_1800_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_proof_1804_; lean_object* v_subst_1805_; uint8_t v___x_1831_; 
lean_inc(v_a_1795_);
v___x_1801_ = l_Lean_Expr_app___override(v_fst_1755_, v_a_1795_);
v___x_1802_ = l_Lean_Expr_bindingBody_x21(v_fst_1759_);
lean_dec(v_fst_1759_);
v___x_1831_ = lean_unbox(v___x_1796_);
lean_dec(v___x_1796_);
switch(v___x_1831_)
{
case 0:
{
lean_del_object(v___x_1769_);
lean_del_object(v___x_1765_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1757_);
lean_del_object(v___x_1749_);
goto v___jp_1824_;
}
case 3:
{
lean_del_object(v___x_1769_);
lean_del_object(v___x_1765_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1757_);
lean_del_object(v___x_1749_);
goto v___jp_1824_;
}
case 5:
{
lean_object* v___x_1832_; lean_object* v_instNew_1834_; lean_object* v___x_1843_; 
lean_del_object(v___x_1769_);
lean_del_object(v___x_1765_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1757_);
lean_del_object(v___x_1749_);
lean_inc_n(v_a_1795_, 2);
v___x_1832_ = lean_array_push(v_fst_1767_, v_a_1795_);
v___x_1843_ = l_Lean_Meta_Sym_inferType(v_a_1795_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = l_Lean_Expr_bindingDomain_x21(v___x_1802_);
v___x_1846_ = lean_expr_instantiate_rev(v___x_1845_, v___x_1832_);
lean_dec_ref(v___x_1845_);
lean_inc_ref(v___x_1846_);
v___x_1847_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_1844_, v___x_1846_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; uint8_t v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = lean_unbox(v_a_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Meta_trySynthInstance(v___x_1846_, v___x_1774_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1868_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1868_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1868_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
if (lean_obj_tag(v_a_1851_) == 1)
{
lean_object* v_a_1855_; 
lean_del_object(v___x_1853_);
lean_dec(v_a_1848_);
v_a_1855_ = lean_ctor_get(v_a_1851_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v_a_1851_, 1);
v_instNew_1834_ = v_a_1855_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1856_; uint8_t v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v_a_1851_);
v___x_1856_ = lean_alloc_ctor(0, 0, 2);
v___x_1857_ = lean_unbox(v_a_1848_);
lean_ctor_set_uint8(v___x_1856_, 0, v___x_1857_);
v___x_1858_ = lean_unbox(v_a_1848_);
lean_dec(v_a_1848_);
lean_ctor_set_uint8(v___x_1856_, 1, v___x_1858_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1856_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1832_);
lean_ctor_set(v___x_1860_, 1, v___x_1800_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_fst_1763_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1802_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1801_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1859_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1864_);
v___x_1866_ = v___x_1853_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1848_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1802_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1800_);
lean_dec(v_fst_1763_);
v_a_1869_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1850_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1850_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_dec(v_a_1848_);
lean_dec_ref(v___x_1846_);
lean_inc(v_a_1795_);
v_instNew_1834_ = v_a_1795_;
goto v___jp_1833_;
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___x_1846_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1802_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1800_);
lean_dec(v_fst_1763_);
v_a_1877_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1847_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1847_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
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
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1802_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1800_);
lean_dec(v_fst_1763_);
v_a_1885_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1843_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1843_);
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
v___jp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_inc_ref(v_instNew_1834_);
v___x_1835_ = l_Lean_Expr_app___override(v___x_1801_, v_instNew_1834_);
v___x_1836_ = lean_array_push(v___x_1832_, v_instNew_1834_);
v___x_1837_ = l_Lean_Expr_bindingBody_x21(v___x_1802_);
lean_dec_ref(v___x_1802_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1800_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_fst_1763_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1837_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1835_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1774_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v_a_1741_ = v___x_1842_;
goto v___jp_1740_;
}
}
case 2:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1795_);
v___x_1894_ = lean_array_push(v_fst_1767_, v_a_1795_);
v___x_1895_ = lean_array_get_borrowed(v___x_1893_, v_argResults_1725_, v_fst_1763_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; 
lean_inc(v_a_1795_);
v___x_1896_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1795_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc_n(v_a_1897_, 2);
lean_dec_ref_known(v___x_1896_, 1);
lean_inc_n(v_a_1795_, 2);
v___x_1898_ = l_Lean_mkAppB(v___x_1801_, v_a_1795_, v_a_1897_);
v___x_1899_ = lean_array_push(v___x_1894_, v_a_1795_);
v___x_1900_ = lean_array_push(v___x_1899_, v_a_1897_);
v_proof_1804_ = v___x_1898_;
v_subst_1805_ = v___x_1900_;
goto v___jp_1803_;
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v___x_1894_);
lean_dec_ref(v___x_1802_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1800_);
lean_del_object(v___x_1769_);
lean_del_object(v___x_1765_);
lean_dec(v_fst_1763_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1757_);
lean_del_object(v___x_1749_);
v_a_1901_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1896_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1896_);
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
}
else
{
lean_object* v_e_x27_1909_; lean_object* v_proof_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_e_x27_1909_ = lean_ctor_get(v___x_1895_, 0);
v_proof_1910_ = lean_ctor_get(v___x_1895_, 1);
lean_inc_ref_n(v_proof_1910_, 2);
lean_inc_ref_n(v_e_x27_1909_, 2);
v___x_1911_ = l_Lean_mkAppB(v___x_1801_, v_e_x27_1909_, v_proof_1910_);
v___x_1912_ = lean_array_push(v___x_1894_, v_e_x27_1909_);
v___x_1913_ = lean_array_push(v___x_1912_, v_proof_1910_);
v_proof_1804_ = v___x_1911_;
v_subst_1805_ = v___x_1913_;
goto v___jp_1803_;
}
}
default: 
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1769_);
lean_del_object(v___x_1765_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1757_);
lean_del_object(v___x_1749_);
v___x_1914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
v___x_1915_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_1914_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref_known(v___x_1915_, 1);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_fst_1767_);
lean_ctor_set(v___x_1916_, 1, v___x_1800_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_fst_1763_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1802_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1801_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1774_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v_a_1741_ = v___x_1920_;
goto v___jp_1740_;
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v___x_1802_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1800_);
lean_dec(v_fst_1767_);
lean_dec(v_fst_1763_);
v_a_1921_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1915_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1915_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
v___jp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1806_ = l_Lean_Expr_bindingBody_x21(v___x_1802_);
lean_dec_ref(v___x_1802_);
v___x_1807_ = l_Lean_Expr_bindingBody_x21(v___x_1806_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = lean_nat_add(v_fst_1763_, v___x_1797_);
lean_dec(v_fst_1763_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v___x_1800_);
lean_ctor_set(v___x_1769_, 0, v_subst_1805_);
v___x_1810_ = v___x_1769_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_subst_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1800_);
v___x_1810_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1810_);
lean_ctor_set(v___x_1765_, 0, v___x_1808_);
v___x_1812_ = v___x_1765_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1812_);
lean_ctor_set(v___x_1761_, 0, v___x_1807_);
v___x_1814_ = v___x_1761_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1814_);
lean_ctor_set(v___x_1757_, 0, v_proof_1804_);
v___x_1816_ = v___x_1757_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_proof_1804_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1816_);
lean_ctor_set(v___x_1749_, 0, v___x_1774_);
v___x_1818_ = v___x_1749_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v_a_1741_ = v___x_1818_;
goto v___jp_1740_;
}
}
}
}
}
}
v___jp_1824_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_inc(v_a_1795_);
v___x_1825_ = lean_array_push(v_fst_1767_, v_a_1795_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1800_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_fst_1763_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1802_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1801_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1774_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v_a_1741_ = v___x_1830_;
goto v___jp_1740_;
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
v___jp_1740_:
{
size_t v___x_1742_; size_t v___x_1743_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1728_, v___x_1742_);
v_i_1728_ = v___x_1743_;
v_b_1729_ = v_a_1741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_1944_, lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1944_, v_as_1945_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v_as_1945_);
lean_dec_ref(v_argResults_1944_);
return v_res_1961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1963_ = lean_unsigned_to_nat(34u);
v___x_1964_ = lean_unsigned_to_nat(402u);
v___x_1965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1966_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1967_ = l_mkPanicMessageWithDecl(v___x_1966_, v___x_1965_, v___x_1964_, v___x_1963_, v___x_1962_);
return v___x_1967_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1970_; lean_object* v_dummy_1971_; 
v___x_1970_ = lean_box(0);
v_dummy_1971_ = l_Lean_Expr_sort___override(v___x_1970_);
return v_dummy_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_1975_, lean_object* v_argKinds_1976_, lean_object* v_type_1977_, lean_object* v_proof_1978_, lean_object* v_argResults_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v_j_2002_; lean_object* v_subst_2003_; lean_object* v_dummy_2004_; lean_object* v_nargs_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_args_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; size_t v_sz_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v_j_2002_ = lean_unsigned_to_nat(0u);
v_subst_2003_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2004_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2005_ = l_Lean_Expr_getAppNumArgs(v_e_1975_);
lean_inc(v_nargs_2005_);
v___x_2006_ = lean_mk_array(v_nargs_2005_, v_dummy_2004_);
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_sub(v_nargs_2005_, v___x_2007_);
lean_dec(v_nargs_2005_);
v_args_2009_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1975_, v___x_2006_, v___x_2008_);
v___x_2010_ = lean_array_get_size(v_argKinds_1976_);
lean_inc_ref(v_argKinds_1976_);
v___x_2011_ = l_Array_toSubarray___redArg(v_argKinds_1976_, v_j_2002_, v___x_2010_);
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_subst_2003_);
lean_ctor_set(v___x_2013_, 1, v___x_2011_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_j_2002_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_type_1977_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_proof_1978_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2012_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v_sz_2018_ = lean_array_size(v_args_2009_);
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1979_, v_args_2009_, v_sz_2018_, v___x_2019_, v___x_2017_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec_ref(v_args_2009_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2091_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2091_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2091_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v_fst_2025_; 
v_fst_2025_ = lean_ctor_get(v_a_2021_, 0);
if (lean_obj_tag(v_fst_2025_) == 0)
{
lean_object* v_snd_2026_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___y_2030_; uint8_t v___y_2031_; lean_object* v_rhs_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_snd_2026_ = lean_ctor_get(v_a_2021_, 1);
lean_inc(v_snd_2026_);
lean_dec(v_a_2021_);
v_fst_2027_ = lean_ctor_get(v_snd_2026_, 0);
lean_inc(v_fst_2027_);
v_snd_2028_ = lean_ctor_get(v_snd_2026_, 1);
lean_inc(v_snd_2028_);
lean_dec(v_snd_2026_);
v_fst_2059_ = lean_ctor_get(v_snd_2028_, 0);
lean_inc(v_fst_2059_);
v_snd_2060_ = lean_ctor_get(v_snd_2028_, 1);
lean_inc(v_snd_2060_);
lean_dec(v_snd_2028_);
v___x_2061_ = l_Lean_Expr_cleanupAnnotations(v_fst_2059_);
v___x_2062_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec(v_snd_2060_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2023_);
lean_dec_ref(v_argKinds_1976_);
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
v___y_1998_ = v___y_1987_;
v___y_1999_ = v___y_1988_;
goto v___jp_1990_;
}
else
{
lean_object* v_arg_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_arg_2063_ = lean_ctor_get(v___x_2061_, 1);
lean_inc_ref(v_arg_2063_);
v___x_2064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2061_);
v___x_2065_ = l_Lean_Expr_isApp(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_arg_2063_);
lean_dec(v_snd_2060_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2023_);
lean_dec_ref(v_argKinds_1976_);
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
v___y_1998_ = v___y_1987_;
v___y_1999_ = v___y_1988_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2064_);
v___x_2067_ = l_Lean_Expr_isApp(v___x_2066_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec(v_snd_2060_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2023_);
lean_dec_ref(v_argKinds_1976_);
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
v___y_1998_ = v___y_1987_;
v___y_1999_ = v___y_1988_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2066_);
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2070_ = l_Lean_Expr_isConstOf(v___x_2068_, v___x_2069_);
lean_dec_ref(v___x_2068_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v_arg_2063_);
lean_dec(v_snd_2060_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2023_);
lean_dec_ref(v_argKinds_1976_);
v___y_1991_ = v___y_1980_;
v___y_1992_ = v___y_1981_;
v___y_1993_ = v___y_1982_;
v___y_1994_ = v___y_1983_;
v___y_1995_ = v___y_1984_;
v___y_1996_ = v___y_1985_;
v___y_1997_ = v___y_1986_;
v___y_1998_ = v___y_1987_;
v___y_1999_ = v___y_1988_;
goto v___jp_1990_;
}
else
{
lean_object* v_snd_2071_; lean_object* v_fst_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_snd_2071_ = lean_ctor_get(v_snd_2060_, 1);
lean_inc(v_snd_2071_);
lean_dec(v_snd_2060_);
v_fst_2072_ = lean_ctor_get(v_snd_2071_, 0);
lean_inc(v_fst_2072_);
lean_dec(v_snd_2071_);
v___x_2073_ = lean_expr_instantiate_rev(v_arg_2063_, v_fst_2072_);
lean_dec(v_fst_2072_);
lean_dec_ref(v_arg_2063_);
v___x_2074_ = lean_nat_dec_lt(v_j_2002_, v___x_2010_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v_argKinds_1976_);
v_rhs_2038_ = v___x_2073_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
v___y_2043_ = v___y_1987_;
v___y_2044_ = v___y_1988_;
goto v___jp_2037_;
}
else
{
if (v___x_2074_ == 0)
{
lean_dec_ref(v_argKinds_1976_);
v_rhs_2038_ = v___x_2073_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
v___y_2043_ = v___y_1987_;
v___y_2044_ = v___y_1988_;
goto v___jp_2037_;
}
else
{
size_t v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_usize_of_nat(v___x_2010_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_2070_, v_argKinds_1976_, v___x_2019_, v___x_2075_);
lean_dec_ref(v_argKinds_1976_);
if (v___x_2076_ == 0)
{
v_rhs_2038_ = v___x_2073_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
v___y_2043_ = v___y_1987_;
v___y_2044_ = v___y_1988_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2073_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v_rhs_2038_ = v_a_2078_;
v___y_2039_ = v___y_1983_;
v___y_2040_ = v___y_1984_;
v___y_2041_ = v___y_1985_;
v___y_2042_ = v___y_1986_;
v___y_2043_ = v___y_1987_;
v___y_2044_ = v___y_1988_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_fst_2027_);
lean_del_object(v___x_2023_);
v_a_2079_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2077_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
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
v___jp_2029_:
{
uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = 0;
v___x_2033_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2033_, 0, v___y_2030_);
lean_ctor_set(v___x_2033_, 1, v_fst_2027_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2, v___x_2032_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 1, v___y_2031_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2033_);
v___x_2035_ = v___x_2023_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
v___jp_2037_:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_Sym_shareCommonInc(v_rhs_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = lean_array_get_size(v_argResults_1979_);
v___x_2048_ = lean_nat_dec_lt(v_j_2002_, v___x_2047_);
if (v___x_2048_ == 0)
{
v___y_2030_ = v_a_2046_;
v___y_2031_ = v___x_2048_;
goto v___jp_2029_;
}
else
{
if (v___x_2048_ == 0)
{
v___y_2030_ = v_a_2046_;
v___y_2031_ = v___x_2048_;
goto v___jp_2029_;
}
else
{
size_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = lean_usize_of_nat(v___x_2047_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_1979_, v___x_2019_, v___x_2049_);
v___y_2030_ = v_a_2046_;
v___y_2031_ = v___x_2050_;
goto v___jp_2029_;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_fst_2027_);
lean_del_object(v___x_2023_);
v_a_2051_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2045_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2045_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; 
lean_inc_ref(v_fst_2025_);
lean_dec(v_a_2021_);
lean_dec_ref(v_argKinds_1976_);
v_val_2087_ = lean_ctor_get(v_fst_2025_, 0);
lean_inc(v_val_2087_);
lean_dec_ref_known(v_fst_2025_, 1);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v_val_2087_);
v___x_2089_ = v___x_2023_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_val_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_argKinds_1976_);
v_a_2092_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2020_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2020_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
v___jp_1990_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_2001_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2000_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2100_, lean_object* v_argKinds_2101_, lean_object* v_type_2102_, lean_object* v_proof_2103_, lean_object* v_argResults_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2100_, v_argKinds_2101_, v_type_2102_, v_proof_2103_, v_argResults_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v_argResults_2104_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2116_, lean_object* v_x_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2128_, 0, v___x_2116_);
lean_ctor_set_uint8(v___x_2128_, 1, v___x_2116_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v___x_24039__boxed_2142_; lean_object* v_res_2143_; 
v___x_24039__boxed_2142_ = lean_unbox(v___x_2130_);
v_res_2143_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_24039__boxed_2142_, v_x_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v_x_2131_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2146_, lean_object* v_argKinds_2147_, lean_object* v_mkNonRflResult_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2160_ = lean_unsigned_to_nat(1u);
v___x_2161_ = lean_nat_sub(v___x_2146_, v___x_2160_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2164_ = 0;
v___x_2165_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2147_, v_mkNonRflResult_2148_, v_x_2149_, v___x_2161_, v___x_2162_, v___x_2163_, v___x_2164_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2166_, lean_object* v_argKinds_2167_, lean_object* v_mkNonRflResult_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2166_, v_argKinds_2167_, v_mkNonRflResult_2168_, v_x_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v_argKinds_2167_);
lean_dec(v___x_2166_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2181_, lean_object* v_thm_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_type_2193_; lean_object* v_proof_2194_; lean_object* v_argKinds_2195_; lean_object* v_mkNonRflResult_2196_; lean_object* v_numArgs_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_type_2193_ = lean_ctor_get(v_thm_2182_, 0);
lean_inc_ref(v_type_2193_);
v_proof_2194_ = lean_ctor_get(v_thm_2182_, 1);
lean_inc_ref(v_proof_2194_);
v_argKinds_2195_ = lean_ctor_get(v_thm_2182_, 2);
lean_inc_ref_n(v_argKinds_2195_, 2);
lean_dec_ref(v_thm_2182_);
lean_inc_ref(v_e_2181_);
v_mkNonRflResult_2196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2196_, 0, v_e_2181_);
lean_closure_set(v_mkNonRflResult_2196_, 1, v_argKinds_2195_);
lean_closure_set(v_mkNonRflResult_2196_, 2, v_type_2193_);
lean_closure_set(v_mkNonRflResult_2196_, 3, v_proof_2194_);
v_numArgs_2197_ = l_Lean_Expr_getAppNumArgs(v_e_2181_);
v___x_2198_ = lean_array_get_size(v_argKinds_2195_);
v___x_2199_ = lean_nat_dec_lt(v___x_2198_, v_numArgs_2197_);
if (v___x_2199_ == 0)
{
uint8_t v___x_2200_; 
v___x_2200_ = lean_nat_dec_lt(v_numArgs_2197_, v___x_2198_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_numArgs_2197_);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_sub(v___x_2198_, v___x_2201_);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2205_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2195_, v_mkNonRflResult_2196_, v_e_2181_, v___x_2202_, v___x_2203_, v___x_2204_, v___x_2200_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec_ref(v_argKinds_2195_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_mkNonRflResult_2196_);
lean_dec_ref(v_argKinds_2195_);
v___x_2206_ = lean_box(v___x_2199_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2207_, 0, v___x_2206_);
v___x_2208_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2207_, v_e_2181_, v_numArgs_2197_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v_numArgs_2197_);
return v___x_2208_;
}
}
else
{
lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___f_2209_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2209_, 0, v___x_2198_);
lean_closure_set(v___f_2209_, 1, v_argKinds_2195_);
lean_closure_set(v___f_2209_, 2, v_mkNonRflResult_2196_);
v___x_2210_ = lean_nat_sub(v_numArgs_2197_, v___x_2198_);
lean_dec(v_numArgs_2197_);
v___x_2211_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2209_, v_e_2181_, v___x_2210_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2212_, lean_object* v_thm_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2212_, v_thm_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_f_2236_; lean_object* v___x_2237_; 
v_f_2236_ = l_Lean_Expr_getAppFn(v_e_2225_);
v___x_2237_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2236_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2253_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2253_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2253_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
switch(lean_obj_tag(v_a_2238_))
{
case 0:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_dec_ref(v_e_2225_);
v___x_2242_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
case 1:
{
lean_object* v_prefixSize_2246_; lean_object* v_suffixSize_2247_; lean_object* v___x_2248_; 
lean_del_object(v___x_2240_);
v_prefixSize_2246_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_prefixSize_2246_);
v_suffixSize_2247_ = lean_ctor_get(v_a_2238_, 1);
lean_inc(v_suffixSize_2247_);
lean_dec_ref_known(v_a_2238_, 2);
v___x_2248_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2225_, v_prefixSize_2246_, v_suffixSize_2247_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_prefixSize_2246_);
return v___x_2248_;
}
case 2:
{
lean_object* v_rewritable_2249_; lean_object* v___x_2250_; 
lean_del_object(v___x_2240_);
v_rewritable_2249_ = lean_ctor_get(v_a_2238_, 0);
lean_inc_ref(v_rewritable_2249_);
lean_dec_ref_known(v_a_2238_, 1);
v___x_2250_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2225_, v_rewritable_2249_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2250_;
}
default: 
{
lean_object* v_thm_2251_; lean_object* v___x_2252_; 
lean_del_object(v___x_2240_);
v_thm_2251_ = lean_ctor_get(v_a_2238_, 0);
lean_inc_ref(v_thm_2251_);
lean_dec_ref_known(v_a_2238_, 1);
v___x_2252_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2225_, v_thm_2251_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v_e_2225_);
v_a_2254_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2237_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2237_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
return v_res_2273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2276_ = lean_unsigned_to_nat(55u);
v___x_2277_ = lean_unsigned_to_nat(489u);
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2280_ = l_mkPanicMessageWithDecl(v___x_2279_, v___x_2278_, v___x_2277_, v___x_2276_, v___x_2275_);
return v___x_2280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2282_ = lean_unsigned_to_nat(11u);
v___x_2283_ = lean_unsigned_to_nat(497u);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2286_ = l_mkPanicMessageWithDecl(v___x_2285_, v___x_2284_, v___x_2283_, v___x_2282_, v___x_2281_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2287_, lean_object* v_e_2288_, lean_object* v_i_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
uint8_t v_cd_2301_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = lean_nat_dec_eq(v_i_2289_, v___x_2304_);
if (v___x_2305_ == 0)
{
if (lean_obj_tag(v_e_2288_) == 5)
{
lean_object* v_fn_2306_; lean_object* v_arg_2307_; lean_object* v___x_2308_; lean_object* v_i_2309_; lean_object* v___x_2310_; 
v_fn_2306_ = lean_ctor_get(v_e_2288_, 0);
lean_inc_ref_n(v_fn_2306_, 2);
v_arg_2307_ = lean_ctor_get(v_e_2288_, 1);
lean_inc_ref(v_arg_2307_);
v___x_2308_ = lean_unsigned_to_nat(1u);
v_i_2309_ = lean_nat_sub(v_i_2289_, v___x_2308_);
v___x_2310_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2287_, v_fn_2306_, v_i_2309_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; uint8_t v___x_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = lean_nat_dec_lt(v_i_2309_, v_stop_2287_);
lean_dec(v_i_2309_);
if (v___x_2312_ == 0)
{
if (lean_obj_tag(v_a_2311_) == 0)
{
uint8_t v_contextDependent_2313_; 
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
v_contextDependent_2313_ = lean_ctor_get_uint8(v_a_2311_, 1);
lean_dec_ref_known(v_a_2311_, 0);
v_cd_2301_ = v_contextDependent_2313_;
goto v___jp_2300_;
}
else
{
lean_object* v_e_x27_2314_; lean_object* v_proof_2315_; uint8_t v_contextDependent_2316_; lean_object* v___x_2317_; 
v_e_x27_2314_ = lean_ctor_get(v_a_2311_, 0);
lean_inc_ref(v_e_x27_2314_);
v_proof_2315_ = lean_ctor_get(v_a_2311_, 1);
lean_inc_ref(v_proof_2315_);
v_contextDependent_2316_ = lean_ctor_get_uint8(v_a_2311_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2311_, 2);
v___x_2317_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2288_, v_fn_2306_, v_arg_2307_, v_e_x27_2314_, v_proof_2315_, v___x_2305_, v_contextDependent_2316_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2317_;
}
}
else
{
lean_object* v___x_2318_; 
lean_inc_ref(v_fn_2306_);
v___x_2318_ = l_Lean_Meta_Sym_inferType(v_fn_2306_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l_Lean_Meta_whnfD(v_a_2319_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
if (lean_obj_tag(v_a_2321_) == 7)
{
lean_object* v_binderType_2322_; lean_object* v_body_2323_; uint8_t v___x_2341_; 
v_binderType_2322_ = lean_ctor_get(v_a_2321_, 1);
lean_inc_ref(v_binderType_2322_);
v_body_2323_ = lean_ctor_get(v_a_2321_, 2);
lean_inc_ref(v_body_2323_);
lean_dec_ref_known(v_a_2321_, 3);
v___x_2341_ = l_Lean_Expr_hasLooseBVars(v_body_2323_);
lean_dec_ref(v_body_2323_);
if (v___x_2341_ == 0)
{
goto v___jp_2324_;
}
else
{
if (v___x_2305_ == 0)
{
lean_dec_ref(v_binderType_2322_);
if (lean_obj_tag(v_a_2311_) == 0)
{
uint8_t v_contextDependent_2342_; 
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
v_contextDependent_2342_ = lean_ctor_get_uint8(v_a_2311_, 1);
lean_dec_ref_known(v_a_2311_, 0);
v_cd_2301_ = v_contextDependent_2342_;
goto v___jp_2300_;
}
else
{
lean_object* v_e_x27_2343_; lean_object* v_proof_2344_; uint8_t v_contextDependent_2345_; lean_object* v___x_2346_; 
v_e_x27_2343_ = lean_ctor_get(v_a_2311_, 0);
lean_inc_ref(v_e_x27_2343_);
v_proof_2344_ = lean_ctor_get(v_a_2311_, 1);
lean_inc_ref(v_proof_2344_);
v_contextDependent_2345_ = lean_ctor_get_uint8(v_a_2311_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2311_, 2);
v___x_2346_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2288_, v_fn_2306_, v_arg_2307_, v_e_x27_2343_, v_proof_2344_, v___x_2305_, v_contextDependent_2345_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2346_;
}
}
else
{
goto v___jp_2324_;
}
}
v___jp_2324_:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Meta_isProp(v_binderType_2322_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; uint8_t v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = lean_unbox(v_a_2326_);
lean_dec(v_a_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_arg_2307_);
v___x_2328_ = lean_sym_simp(v_arg_2307_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2288_, v_fn_2306_, v_arg_2307_, v_a_2311_, v_a_2329_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2330_;
}
else
{
lean_dec(v_a_2311_);
lean_dec_ref(v_arg_2307_);
lean_dec_ref_known(v_e_2288_, 2);
lean_dec_ref(v_fn_2306_);
return v___x_2328_;
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2331_, 0, v___x_2305_);
lean_ctor_set_uint8(v___x_2331_, 1, v___x_2305_);
v___x_2332_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2288_, v_fn_2306_, v_arg_2307_, v_a_2311_, v___x_2331_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2332_;
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_a_2311_);
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
v_a_2333_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2325_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2325_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v_a_2321_);
lean_dec(v_a_2311_);
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2348_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2347_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2348_;
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2311_);
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
v_a_2349_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2320_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2320_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2311_);
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
v_a_2357_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2318_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2318_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
else
{
lean_dec(v_i_2309_);
lean_dec_ref(v_arg_2307_);
lean_dec_ref(v_fn_2306_);
lean_dec_ref_known(v_e_2288_, 2);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec_ref(v_e_2288_);
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2366_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2365_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2366_;
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec_ref(v_e_2288_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
v___jp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_2301_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2369_, lean_object* v_e_2370_, lean_object* v_i_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2369_, v_e_2370_, v_i_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec(v_i_2371_);
lean_dec(v_stop_2369_);
return v_res_2382_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2385_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2386_ = lean_unsigned_to_nat(2u);
v___x_2387_ = lean_unsigned_to_nat(472u);
v___x_2388_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2390_ = l_mkPanicMessageWithDecl(v___x_2389_, v___x_2388_, v___x_2387_, v___x_2386_, v___x_2385_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2391_, lean_object* v_start_2392_, lean_object* v_stop_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
uint8_t v___x_2404_; 
v___x_2404_ = lean_nat_dec_lt(v_start_2392_, v_stop_2393_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v_e_2391_);
v___x_2405_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2406_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2405_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
return v___x_2406_;
}
else
{
lean_object* v_numArgs_2407_; uint8_t v___x_2408_; 
v_numArgs_2407_ = l_Lean_Expr_getAppNumArgs(v_e_2391_);
v___x_2408_ = lean_nat_dec_lt(v_numArgs_2407_, v_start_2392_);
if (v___x_2408_ == 0)
{
lean_object* v_numArgs_2409_; lean_object* v_stop_2410_; lean_object* v___x_2411_; 
v_numArgs_2409_ = lean_nat_sub(v_numArgs_2407_, v_start_2392_);
lean_dec(v_numArgs_2407_);
v_stop_2410_ = lean_nat_sub(v_stop_2393_, v_start_2392_);
v___x_2411_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2410_, v_e_2391_, v_numArgs_2409_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_numArgs_2409_);
lean_dec(v_stop_2410_);
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec(v_numArgs_2407_);
lean_dec_ref(v_e_2391_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2414_, lean_object* v_start_2415_, lean_object* v_stop_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2414_, v_start_2415_, v_stop_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec(v_stop_2416_);
lean_dec(v_start_2415_);
return v_res_2427_;
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
