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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(lean_object* v_e_300_, lean_object* v_f_301_, lean_object* v_a_302_, lean_object* v_ar_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
if (lean_obj_tag(v_ar_303_) == 0)
{
uint8_t v_contextDependent_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec_ref(v_a_302_);
lean_dec_ref(v_f_301_);
lean_dec_ref(v_e_300_);
v_contextDependent_311_ = lean_ctor_get_uint8(v_ar_303_, 1);
lean_dec_ref_known(v_ar_303_, 0);
v___x_312_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_311_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v_e_x27_314_; lean_object* v_proof_315_; uint8_t v_contextDependent_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_387_; 
v_e_x27_314_ = lean_ctor_get(v_ar_303_, 0);
v_proof_315_ = lean_ctor_get(v_ar_303_, 1);
v_contextDependent_316_ = lean_ctor_get_uint8(v_ar_303_, sizeof(void*)*2 + 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_ar_303_);
if (v_isSharedCheck_387_ == 0)
{
v___x_318_ = v_ar_303_;
v_isShared_319_ = v_isSharedCheck_387_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_proof_315_);
lean_inc(v_e_x27_314_);
lean_dec(v_ar_303_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_387_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; 
lean_inc_ref(v_a_302_);
v___x_320_ = l_Lean_Meta_Sym_inferType(v_a_302_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc_n(v_a_321_, 2);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_321_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = l_Lean_Meta_Sym_inferType(v_e_300_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_n(v_a_325_, 2);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_325_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
lean_inc_ref(v_e_x27_314_);
lean_inc_ref(v_f_301_);
v___x_328_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_301_, v_e_x27_314_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_346_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_346_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_346_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_346_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_341_; 
v___x_333_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v_a_327_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_323_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_mkConst(v___x_333_, v___x_336_);
v___x_338_ = l_Lean_mkApp6(v___x_337_, v_a_321_, v_a_325_, v_a_302_, v_e_x27_314_, v_f_301_, v_proof_315_);
v___x_339_ = 0;
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_338_);
lean_ctor_set(v___x_318_, 0, v_a_329_);
v___x_341_ = v___x_318_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_329_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_338_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, sizeof(void*)*2 + 1, v_contextDependent_316_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*2, v___x_339_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_341_);
v___x_343_ = v___x_331_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_327_);
lean_dec(v_a_325_);
lean_dec(v_a_323_);
lean_dec(v_a_321_);
lean_del_object(v___x_318_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_e_x27_314_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_f_301_);
v_a_347_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_328_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_328_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_a_325_);
lean_dec(v_a_323_);
lean_dec(v_a_321_);
lean_del_object(v___x_318_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_e_x27_314_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_f_301_);
v_a_355_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_326_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_326_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_a_323_);
lean_dec(v_a_321_);
lean_del_object(v___x_318_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_e_x27_314_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_f_301_);
v_a_363_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_324_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_324_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_321_);
lean_del_object(v___x_318_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_e_x27_314_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_f_301_);
lean_dec_ref(v_e_300_);
v_a_371_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_322_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_322_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_318_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_e_x27_314_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_f_301_);
lean_dec_ref(v_e_300_);
v_a_379_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_320_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_320_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg___boxed(lean_object* v_e_388_, lean_object* v_f_389_, lean_object* v_a_390_, lean_object* v_ar_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_388_, v_f_389_, v_a_390_, v_ar_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg(lean_object* v_e_400_, lean_object* v_f_401_, lean_object* v_a_402_, lean_object* v_ar_403_, lean_object* v_x_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_400_, v_f_401_, v_a_402_, v_ar_403_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___boxed(lean_object* v_e_413_, lean_object* v_f_414_, lean_object* v_a_415_, lean_object* v_ar_416_, lean_object* v_x_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Sym_Simp_mkCongrArg(v_e_413_, v_f_414_, v_a_415_, v_ar_416_, v_x_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* v_msgData_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; lean_object* v_env_433_; uint8_t v___x_434_; lean_object* v_env_435_; lean_object* v___x_436_; lean_object* v_toCold_437_; lean_object* v_mctx_438_; lean_object* v_lctx_439_; lean_object* v_options_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_432_ = lean_st_ref_get(v___y_430_);
v_env_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc_ref(v_env_433_);
lean_dec(v___x_432_);
v___x_434_ = 0;
v_env_435_ = l_Lean_Environment_setRecordingDeps(v_env_433_, v___x_434_);
v___x_436_ = lean_st_ref_get(v___y_428_);
v_toCold_437_ = lean_ctor_get(v___y_429_, 0);
v_mctx_438_ = lean_ctor_get(v___x_436_, 0);
lean_inc_ref(v_mctx_438_);
lean_dec(v___x_436_);
v_lctx_439_ = lean_ctor_get(v___y_427_, 2);
v_options_440_ = lean_ctor_get(v_toCold_437_, 2);
lean_inc_ref(v_options_440_);
lean_inc_ref(v_lctx_439_);
v___x_441_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_441_, 0, v_env_435_);
lean_ctor_set(v___x_441_, 1, v_mctx_438_);
lean_ctor_set(v___x_441_, 2, v_lctx_439_);
lean_ctor_set(v___x_441_, 3, v_options_440_);
v___x_442_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v_msgData_426_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* v_msgData_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_ref_457_; lean_object* v___x_458_; lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_ref_457_ = lean_ctor_get(v___y_454_, 2);
v___x_458_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_inc(v_ref_457_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_ref_457_);
lean_ctor_set(v___x_463_, 1, v_a_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 1);
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* v_e_481_, lean_object* v_f_482_, lean_object* v_a_483_, lean_object* v_f_x27_484_, lean_object* v_hf_485_, uint8_t v_done_486_, uint8_t v_contextDependent_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
lean_inc_ref(v_f_482_);
v___x_495_ = l_Lean_Meta_Sym_inferType(v_f_482_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = l_Lean_Meta_whnfD(v_a_496_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
if (lean_obj_tag(v_a_498_) == 7)
{
lean_object* v_binderName_499_; lean_object* v_body_500_; lean_object* v___x_501_; 
v_binderName_499_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_binderName_499_);
v_body_500_ = lean_ctor_get(v_a_498_, 2);
lean_inc_ref(v_body_500_);
lean_dec_ref_known(v_a_498_, 3);
lean_inc_ref(v_a_483_);
v___x_501_ = l_Lean_Meta_Sym_inferType(v_a_483_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc_n(v_a_502_, 2);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_502_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_Meta_Sym_inferType(v_e_481_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_506_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = 0;
lean_inc(v_a_502_);
v___x_510_ = l_Lean_mkLambda(v_binderName_499_, v___x_509_, v_a_502_, v_body_500_);
lean_inc_ref(v_a_483_);
lean_inc_ref(v_f_x27_484_);
v___x_511_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_x27_484_, v_a_483_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_526_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_526_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_508_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_519_, 0, v_a_504_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_mkConst(v___x_516_, v___x_519_);
v___x_521_ = l_Lean_mkApp6(v___x_520_, v_a_502_, v___x_510_, v_f_482_, v_f_x27_484_, v_hf_485_, v_a_483_);
v___x_522_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_522_, 0, v_a_512_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*2, v_done_486_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*2 + 1, v_contextDependent_487_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_522_);
v___x_524_ = v___x_514_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v___x_510_);
lean_dec(v_a_508_);
lean_dec(v_a_504_);
lean_dec(v_a_502_);
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
v_a_527_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_511_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_511_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_504_);
lean_dec(v_a_502_);
lean_dec_ref(v_body_500_);
lean_dec(v_binderName_499_);
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
v_a_535_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_507_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_507_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_504_);
lean_dec(v_a_502_);
lean_dec_ref(v_body_500_);
lean_dec(v_binderName_499_);
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
v_a_543_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_505_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_505_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_a_502_);
lean_dec_ref(v_body_500_);
lean_dec(v_binderName_499_);
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
lean_dec_ref(v_e_481_);
v_a_551_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_503_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_503_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v_body_500_);
lean_dec(v_binderName_499_);
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
lean_dec_ref(v_e_481_);
v_a_559_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_501_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_501_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
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
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_a_498_);
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_e_481_);
v___x_567_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
v___x_568_ = l_Lean_indentExpr(v_f_482_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_569_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_570_;
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
lean_dec_ref(v_e_481_);
v_a_571_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_497_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_497_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_hf_485_);
lean_dec_ref(v_f_x27_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_f_482_);
lean_dec_ref(v_e_481_);
v_a_579_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_495_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_495_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* v_e_587_, lean_object* v_f_588_, lean_object* v_a_589_, lean_object* v_f_x27_590_, lean_object* v_hf_591_, lean_object* v_done_592_, lean_object* v_contextDependent_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
uint8_t v_done_boxed_601_; uint8_t v_contextDependent_boxed_602_; lean_object* v_res_603_; 
v_done_boxed_601_ = lean_unbox(v_done_592_);
v_contextDependent_boxed_602_ = lean_unbox(v_contextDependent_593_);
v_res_603_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_587_, v_f_588_, v_a_589_, v_f_x27_590_, v_hf_591_, v_done_boxed_601_, v_contextDependent_boxed_602_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* v_e_604_, lean_object* v_f_605_, lean_object* v_a_606_, lean_object* v_f_x27_607_, lean_object* v_hf_608_, lean_object* v_x_609_, uint8_t v_done_610_, uint8_t v_contextDependent_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_604_, v_f_605_, v_a_606_, v_f_x27_607_, v_hf_608_, v_done_610_, v_contextDependent_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* v_e_620_, lean_object* v_f_621_, lean_object* v_a_622_, lean_object* v_f_x27_623_, lean_object* v_hf_624_, lean_object* v_x_625_, lean_object* v_done_626_, lean_object* v_contextDependent_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
uint8_t v_done_boxed_635_; uint8_t v_contextDependent_boxed_636_; lean_object* v_res_637_; 
v_done_boxed_635_ = lean_unbox(v_done_626_);
v_contextDependent_boxed_636_ = lean_unbox(v_contextDependent_627_);
v_res_637_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(v_e_620_, v_f_621_, v_a_622_, v_f_x27_623_, v_hf_624_, v_x_625_, v_done_boxed_635_, v_contextDependent_boxed_636_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* v_00_u03b1_638_, lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_639_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* v_00_u03b1_648_, lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(v_00_u03b1_648_, v_msg_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_657_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_6782__overap_671_; lean_object* v___x_672_; 
v___x_670_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_6782__overap_671_ = lean_panic_fn_borrowed(v___x_670_, v_msg_659_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
v___x_672_ = lean_apply_10(v___x_6782__overap_671_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, lean_box(0));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
return v_res_684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_689_ = lean_unsigned_to_nat(55u);
v___x_690_ = lean_unsigned_to_nat(139u);
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_693_ = l_mkPanicMessageWithDecl(v___x_692_, v___x_691_, v___x_690_, v___x_689_, v___x_688_);
return v___x_693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_695_ = lean_unsigned_to_nat(13u);
v___x_696_ = lean_unsigned_to_nat(151u);
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* v_simpFn_700_, lean_object* v_e_701_, lean_object* v_i_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_nat_dec_eq(v_i_702_, v___x_713_);
if (v___x_714_ == 0)
{
switch(lean_obj_tag(v_e_701_))
{
case 10:
{
lean_object* v_expr_715_; 
v_expr_715_ = lean_ctor_get(v_e_701_, 1);
lean_inc_ref(v_expr_715_);
lean_dec_ref_known(v_e_701_, 2);
v_e_701_ = v_expr_715_;
goto _start;
}
case 5:
{
lean_object* v_fn_717_; lean_object* v_arg_718_; lean_object* v___x_719_; lean_object* v_i_720_; lean_object* v___x_721_; 
v_fn_717_ = lean_ctor_get(v_e_701_, 0);
lean_inc_ref_n(v_fn_717_, 2);
v_arg_718_ = lean_ctor_get(v_e_701_, 1);
lean_inc_ref(v_arg_718_);
v___x_719_ = lean_unsigned_to_nat(1u);
v_i_720_ = lean_nat_sub(v_i_702_, v___x_719_);
v___x_721_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_700_, v_fn_717_, v_i_720_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_i_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
lean_inc_ref(v_fn_717_);
v___x_723_ = l_Lean_Meta_Sym_inferType(v_fn_717_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_Lean_Meta_whnfD(v_a_724_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_760_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_760_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_760_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_760_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_a_726_) == 7)
{
lean_object* v_binderType_730_; lean_object* v_body_731_; uint8_t v___x_732_; 
v_binderType_730_ = lean_ctor_get(v_a_726_, 1);
lean_inc_ref(v_binderType_730_);
v_body_731_ = lean_ctor_get(v_a_726_, 2);
lean_inc_ref(v_body_731_);
lean_dec_ref_known(v_a_726_, 3);
v___x_732_ = l_Lean_Expr_hasLooseBVars(v_body_731_);
lean_dec_ref(v_body_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_del_object(v___x_728_);
v___x_733_ = l_Lean_Meta_isProp(v_binderType_730_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_inc(v_a_711_);
lean_inc_ref(v_a_710_);
lean_inc(v_a_709_);
lean_inc_ref(v_a_708_);
lean_inc(v_a_707_);
lean_inc_ref(v_a_706_);
lean_inc(v_a_705_);
lean_inc_ref(v_a_704_);
lean_inc(v_a_703_);
lean_inc_ref(v_arg_718_);
v___x_736_ = lean_sym_simp(v_arg_718_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_701_, v_fn_717_, v_arg_718_, v_a_722_, v_a_737_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_738_;
}
else
{
lean_dec(v_a_722_);
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
return v___x_736_;
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_739_, 0, v___x_714_);
lean_ctor_set_uint8(v___x_739_, 1, v___x_714_);
v___x_740_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_701_, v_fn_717_, v_arg_718_, v_a_722_, v___x_739_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_740_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_722_);
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
v_a_741_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_733_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_733_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_730_);
if (lean_obj_tag(v_a_722_) == 0)
{
uint8_t v_contextDependent_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
v_contextDependent_749_ = lean_ctor_get_uint8(v_a_722_, 1);
lean_dec_ref_known(v_a_722_, 0);
v___x_750_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_749_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_750_);
v___x_752_ = v___x_728_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v_e_x27_754_; lean_object* v_proof_755_; uint8_t v_contextDependent_756_; lean_object* v___x_757_; 
lean_del_object(v___x_728_);
v_e_x27_754_ = lean_ctor_get(v_a_722_, 0);
lean_inc_ref(v_e_x27_754_);
v_proof_755_ = lean_ctor_get(v_a_722_, 1);
lean_inc_ref(v_proof_755_);
v_contextDependent_756_ = lean_ctor_get_uint8(v_a_722_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_722_, 2);
v___x_757_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_701_, v_fn_717_, v_arg_718_, v_e_x27_754_, v_proof_755_, v___x_714_, v_contextDependent_756_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_757_;
}
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_del_object(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v_a_722_);
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
v___x_758_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
v___x_759_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_758_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_759_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_722_);
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
v_a_761_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_725_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_725_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v_a_722_);
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
v_a_769_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_723_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_723_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_dec_ref(v_arg_718_);
lean_dec_ref_known(v_e_701_, 2);
lean_dec_ref(v_fn_717_);
return v___x_721_;
}
}
default: 
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_e_701_);
lean_dec_ref(v_simpFn_700_);
v___x_777_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
v___x_778_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_777_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_778_;
}
}
}
else
{
lean_object* v___x_779_; 
lean_inc(v_a_711_);
lean_inc_ref(v_a_710_);
lean_inc(v_a_709_);
lean_inc_ref(v_a_708_);
lean_inc(v_a_707_);
lean_inc_ref(v_a_706_);
lean_inc(v_a_705_);
lean_inc_ref(v_a_704_);
lean_inc(v_a_703_);
v___x_779_ = lean_apply_11(v_simpFn_700_, v_e_701_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, lean_box(0));
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* v_simpFn_780_, lean_object* v_e_781_, lean_object* v_i_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_780_, v_e_781_, v_i_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec(v_i_782_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* v_e_794_, lean_object* v_numArgs_795_, lean_object* v_simpFn_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_796_, v_e_794_, v_numArgs_795_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* v_e_808_, lean_object* v_numArgs_809_, lean_object* v_simpFn_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_808_, v_numArgs_809_, v_simpFn_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_numArgs_809_);
return v_res_821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_824_ = lean_unsigned_to_nat(13u);
v___x_825_ = lean_unsigned_to_nat(188u);
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_828_ = l_mkPanicMessageWithDecl(v___x_827_, v___x_826_, v___x_825_, v___x_824_, v___x_823_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* v_simpFn_829_, lean_object* v_e_830_, lean_object* v_i_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_nat_dec_eq(v_i_831_, v___x_842_);
if (v___x_843_ == 0)
{
if (lean_obj_tag(v_e_830_) == 5)
{
lean_object* v_fn_844_; lean_object* v_arg_845_; lean_object* v___x_846_; lean_object* v_i_847_; lean_object* v___x_848_; 
v_fn_844_ = lean_ctor_get(v_e_830_, 0);
lean_inc_ref_n(v_fn_844_, 2);
v_arg_845_ = lean_ctor_get(v_e_830_, 1);
lean_inc_ref(v_arg_845_);
v___x_846_ = lean_unsigned_to_nat(1u);
v_i_847_ = lean_nat_sub(v_i_831_, v___x_846_);
v___x_848_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_829_, v_fn_844_, v_i_847_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec(v_i_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
if (lean_obj_tag(v_a_849_) == 0)
{
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_fn_844_);
lean_dec_ref_known(v_e_830_, 2);
return v___x_848_;
}
else
{
lean_object* v_e_x27_850_; lean_object* v_proof_851_; uint8_t v_done_852_; uint8_t v_contextDependent_853_; lean_object* v___x_854_; 
lean_inc_ref(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_e_x27_850_ = lean_ctor_get(v_a_849_, 0);
lean_inc_ref(v_e_x27_850_);
v_proof_851_ = lean_ctor_get(v_a_849_, 1);
lean_inc_ref(v_proof_851_);
v_done_852_ = lean_ctor_get_uint8(v_a_849_, sizeof(void*)*2);
v_contextDependent_853_ = lean_ctor_get_uint8(v_a_849_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_849_, 2);
v___x_854_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_830_, v_fn_844_, v_arg_845_, v_e_x27_850_, v_proof_851_, v_done_852_, v_contextDependent_853_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_854_;
}
}
else
{
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_fn_844_);
lean_dec_ref_known(v_e_830_, 2);
return v___x_848_;
}
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref(v_e_830_);
lean_dec_ref(v_simpFn_829_);
v___x_855_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
v___x_856_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_855_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_856_;
}
}
else
{
lean_object* v___x_857_; 
lean_inc(v_a_840_);
lean_inc_ref(v_a_839_);
lean_inc(v_a_838_);
lean_inc_ref(v_a_837_);
lean_inc(v_a_836_);
lean_inc_ref(v_a_835_);
lean_inc(v_a_834_);
lean_inc_ref(v_a_833_);
lean_inc(v_a_832_);
v___x_857_ = lean_apply_11(v_simpFn_829_, v_e_830_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, lean_box(0));
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* v_simpFn_858_, lean_object* v_e_859_, lean_object* v_i_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_858_, v_e_859_, v_i_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec(v_i_860_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* v_e_872_, lean_object* v_numArgs_873_, lean_object* v_simpFn_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_874_, v_e_872_, v_numArgs_873_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* v_e_886_, lean_object* v_numArgs_887_, lean_object* v_simpFn_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_886_, v_numArgs_887_, v_simpFn_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec(v_numArgs_887_);
return v_res_899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_Expr_isForall(v_type_903_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_whnfD(v_type_903_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Expr_isForall(v_a_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v___x_915_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1);
v___x_916_ = l_Lean_MessageData_ofExpr(v_a_913_);
v___x_917_ = l_Lean_indentD(v___x_916_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_915_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_918_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_Sym_shareCommonInc(v_a_913_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
return v___x_928_;
}
}
else
{
return v___x_912_;
}
}
else
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_type_903_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_938_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_863__overap_949_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_863__overap_949_ = lean_panic_fn_borrowed(v___x_948_, v_msg_940_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
v___x_950_ = lean_apply_7(v___x_863__overap_949_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, lean_box(0));
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_962_ = lean_unsigned_to_nat(47u);
v___x_963_ = lean_unsigned_to_nat(219u);
v___x_964_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_965_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_966_ = l_mkPanicMessageWithDecl(v___x_965_, v___x_964_, v___x_963_, v___x_962_, v___x_961_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_967_, lean_object* v_n_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_zero_976_; uint8_t v_isZero_977_; 
v_zero_976_ = lean_unsigned_to_nat(0u);
v_isZero_977_ = lean_nat_dec_eq(v_n_968_, v_zero_976_);
if (v_isZero_977_ == 1)
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Meta_Sym_inferType(v_e_967_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_978_;
}
else
{
lean_object* v_one_979_; lean_object* v_n_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_one_979_ = lean_unsigned_to_nat(1u);
v_n_980_ = lean_nat_sub(v_n_968_, v_one_979_);
v___x_981_ = l_Lean_Expr_appFn_x21(v_e_967_);
lean_dec_ref(v_e_967_);
v___x_982_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_981_, v_n_980_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_n_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_983_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_995_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_995_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_995_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_995_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
if (lean_obj_tag(v_a_985_) == 7)
{
lean_object* v_body_989_; lean_object* v___x_991_; 
v_body_989_ = lean_ctor_get(v_a_985_, 2);
lean_inc_ref(v_body_989_);
lean_dec_ref_known(v_a_985_, 3);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_body_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_body_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_del_object(v___x_987_);
lean_dec(v_a_985_);
v___x_993_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_994_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_993_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_994_;
}
}
}
else
{
return v___x_984_;
}
}
else
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_996_, lean_object* v_n_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_996_, v_n_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_n_997_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_1006_, lean_object* v_a_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___y_1016_; lean_object* v___x_1019_; uint8_t v_debug_1020_; 
v___x_1019_ = lean_st_ref_get(v___y_1009_);
v_debug_1020_ = lean_ctor_get_uint8(v___x_1019_, sizeof(void*)*12);
lean_dec(v___x_1019_);
if (v_debug_1020_ == 0)
{
v___y_1016_ = v___y_1009_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1006_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1022_; 
lean_dec_ref_known(v___x_1021_, 1);
v___x_1022_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_dec_ref_known(v___x_1022_, 1);
v___y_1016_ = v___y_1009_;
goto v___jp_1015_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_a_1007_);
lean_dec_ref(v_f_1006_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_a_1007_);
lean_dec_ref(v_f_1006_);
v_a_1031_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1021_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1021_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = l_Lean_Expr_app___override(v_f_1006_, v_a_1007_);
v___x_1018_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1017_, v___y_1016_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_1039_, lean_object* v_a_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_1039_, v_a_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_1049_, lean_object* v_a_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_1049_, v_a_1050_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_1062_, lean_object* v_a_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_1062_, v_a_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_27995__overap_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_27995__overap_1087_ = lean_panic_fn_borrowed(v___x_1086_, v_msg_1075_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
v___x_1088_ = lean_apply_10(v___x_27995__overap_1087_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, lean_box(0));
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
return v_res_1100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_1106_ = l_Lean_Expr_const___override(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1109_ = lean_unsigned_to_nat(52u);
v___x_1110_ = lean_unsigned_to_nat(281u);
v___x_1111_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1113_ = l_mkPanicMessageWithDecl(v___x_1112_, v___x_1111_, v___x_1110_, v___x_1109_, v___x_1108_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1115_ = lean_unsigned_to_nat(52u);
v___x_1116_ = lean_unsigned_to_nat(273u);
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1119_ = l_mkPanicMessageWithDecl(v___x_1118_, v___x_1117_, v___x_1116_, v___x_1115_, v___x_1114_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1121_ = lean_unsigned_to_nat(52u);
v___x_1122_ = lean_unsigned_to_nat(288u);
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1125_ = l_mkPanicMessageWithDecl(v___x_1124_, v___x_1123_, v___x_1122_, v___x_1121_, v___x_1120_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1127_ = lean_unsigned_to_nat(26u);
v___x_1128_ = lean_unsigned_to_nat(266u);
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1131_ = l_mkPanicMessageWithDecl(v___x_1130_, v___x_1129_, v___x_1128_, v___x_1127_, v___x_1126_);
return v___x_1131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1137_, lean_object* v_e_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_nat_dec_eq(v_i_1137_, v___x_1149_);
if (v___x_1150_ == 0)
{
if (lean_obj_tag(v_e_1138_) == 5)
{
lean_object* v_fn_1151_; lean_object* v_arg_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_fn_1151_ = lean_ctor_get(v_e_1138_, 0);
lean_inc_ref_n(v_fn_1151_, 2);
v_arg_1152_ = lean_ctor_get(v_e_1138_, 1);
lean_inc_ref(v_arg_1152_);
lean_dec_ref_known(v_e_1138_, 2);
v___x_1153_ = 1;
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_sub(v_i_1137_, v___x_1154_);
v___x_1156_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1155_, v_fn_1151_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v_fst_1158_; lean_object* v_snd_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1414_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v_fst_1158_ = lean_ctor_get(v_a_1157_, 0);
v_snd_1159_ = lean_ctor_get(v_a_1157_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1161_ = v_a_1157_;
v_isShared_1162_ = v_isSharedCheck_1414_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_snd_1159_);
lean_inc(v_fst_1158_);
lean_dec(v_a_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1414_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; 
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc(v_a_1145_);
lean_inc_ref(v_a_1144_);
lean_inc(v_a_1143_);
lean_inc_ref(v_a_1142_);
lean_inc(v_a_1141_);
lean_inc_ref(v_a_1140_);
lean_inc(v_a_1139_);
lean_inc_ref(v_arg_1152_);
v___x_1163_ = lean_sym_simp(v_arg_1152_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1405_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1405_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1405_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
uint8_t v___y_1169_; 
if (lean_obj_tag(v_fst_1158_) == 0)
{
lean_dec(v_snd_1159_);
if (lean_obj_tag(v_a_1164_) == 0)
{
uint8_t v_contextDependent_1178_; 
lean_dec(v___x_1155_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_contextDependent_1178_ = lean_ctor_get_uint8(v_fst_1158_, 1);
lean_dec_ref_known(v_fst_1158_, 0);
if (v_contextDependent_1178_ == 0)
{
uint8_t v_contextDependent_1179_; 
v_contextDependent_1179_ = lean_ctor_get_uint8(v_a_1164_, 1);
lean_dec_ref_known(v_a_1164_, 0);
v___y_1169_ = v_contextDependent_1179_;
goto v___jp_1168_;
}
else
{
lean_dec_ref_known(v_a_1164_, 0);
v___y_1169_ = v___x_1153_;
goto v___jp_1168_;
}
}
else
{
uint8_t v_contextDependent_1180_; lean_object* v_e_x27_1181_; lean_object* v_proof_1182_; uint8_t v_contextDependent_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1260_; 
lean_del_object(v___x_1166_);
lean_del_object(v___x_1161_);
v_contextDependent_1180_ = lean_ctor_get_uint8(v_fst_1158_, 1);
lean_dec_ref_known(v_fst_1158_, 0);
v_e_x27_1181_ = lean_ctor_get(v_a_1164_, 0);
v_proof_1182_ = lean_ctor_get(v_a_1164_, 1);
v_contextDependent_1183_ = lean_ctor_get_uint8(v_a_1164_, sizeof(void*)*2 + 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1185_ = v_a_1164_;
v_isShared_1186_ = v_isSharedCheck_1260_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_proof_1182_);
lean_inc(v_e_x27_1181_);
lean_dec(v_a_1164_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1260_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; 
lean_inc_ref(v_fn_1151_);
v___x_1187_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1151_, v___x_1155_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v___x_1155_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_1188_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
if (lean_obj_tag(v_a_1190_) == 7)
{
lean_object* v_binderType_1191_; lean_object* v_body_1192_; lean_object* v___x_1193_; 
v_binderType_1191_ = lean_ctor_get(v_a_1190_, 1);
lean_inc_ref(v_binderType_1191_);
v_body_1192_ = lean_ctor_get(v_a_1190_, 2);
lean_inc_ref(v_body_1192_);
lean_dec_ref_known(v_a_1190_, 3);
lean_inc_ref(v_e_x27_1181_);
lean_inc_ref(v_fn_1151_);
v___x_1193_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1151_, v_e_x27_1181_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
lean_inc_ref(v_binderType_1191_);
v___x_1195_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1191_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
lean_inc_ref(v_body_1192_);
v___x_1197_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1192_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1217_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1217_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1217_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___y_1209_; 
v___x_1202_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1198_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_a_1196_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_mkConst(v___x_1202_, v___x_1205_);
lean_inc_ref(v_body_1192_);
v___x_1207_ = l_Lean_mkApp6(v___x_1206_, v_binderType_1191_, v_body_1192_, v_arg_1152_, v_e_x27_1181_, v_fn_1151_, v_proof_1182_);
if (v_contextDependent_1180_ == 0)
{
v___y_1209_ = v_contextDependent_1183_;
goto v___jp_1208_;
}
else
{
v___y_1209_ = v___x_1153_;
goto v___jp_1208_;
}
v___jp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1207_);
lean_ctor_set(v___x_1185_, 0, v_a_1194_);
v___x_1211_ = v___x_1185_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1194_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1207_);
v___x_1211_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*2, v___x_1150_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*2 + 1, v___y_1209_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v_body_1192_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1212_);
v___x_1214_ = v___x_1200_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1196_);
lean_dec(v_a_1194_);
lean_dec_ref(v_body_1192_);
lean_dec_ref(v_binderType_1191_);
lean_del_object(v___x_1185_);
lean_dec_ref(v_proof_1182_);
lean_dec_ref(v_e_x27_1181_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1218_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1197_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1197_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_a_1194_);
lean_dec_ref(v_body_1192_);
lean_dec_ref(v_binderType_1191_);
lean_del_object(v___x_1185_);
lean_dec_ref(v_proof_1182_);
lean_dec_ref(v_e_x27_1181_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1226_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1195_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1195_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_body_1192_);
lean_dec_ref(v_binderType_1191_);
lean_del_object(v___x_1185_);
lean_dec_ref(v_proof_1182_);
lean_dec_ref(v_e_x27_1181_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1234_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1193_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1193_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
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
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_a_1190_);
lean_del_object(v___x_1185_);
lean_dec_ref(v_proof_1182_);
lean_dec_ref(v_e_x27_1181_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1243_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1242_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1243_;
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_del_object(v___x_1185_);
lean_dec_ref(v_proof_1182_);
lean_dec_ref(v_e_x27_1181_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1244_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1189_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1189_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_del_object(v___x_1185_);
lean_dec_ref(v_proof_1182_);
lean_dec_ref(v_e_x27_1181_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1252_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1187_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1187_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1166_);
lean_del_object(v___x_1161_);
lean_dec(v___x_1155_);
if (lean_obj_tag(v_a_1164_) == 0)
{
lean_object* v_e_x27_1261_; lean_object* v_proof_1262_; uint8_t v_contextDependent_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1331_; 
v_e_x27_1261_ = lean_ctor_get(v_fst_1158_, 0);
v_proof_1262_ = lean_ctor_get(v_fst_1158_, 1);
v_contextDependent_1263_ = lean_ctor_get_uint8(v_fst_1158_, sizeof(void*)*2 + 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_fst_1158_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1265_ = v_fst_1158_;
v_isShared_1266_ = v_isSharedCheck_1331_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_proof_1262_);
lean_inc(v_e_x27_1261_);
lean_dec(v_fst_1158_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1331_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
uint8_t v_contextDependent_1267_; lean_object* v___x_1268_; 
v_contextDependent_1267_ = lean_ctor_get_uint8(v_a_1164_, 1);
lean_dec_ref_known(v_a_1164_, 0);
v___x_1268_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1159_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
if (lean_obj_tag(v_a_1269_) == 7)
{
lean_object* v_binderType_1270_; lean_object* v_body_1271_; lean_object* v___x_1272_; 
v_binderType_1270_ = lean_ctor_get(v_a_1269_, 1);
lean_inc_ref(v_binderType_1270_);
v_body_1271_ = lean_ctor_get(v_a_1269_, 2);
lean_inc_ref(v_body_1271_);
lean_dec_ref_known(v_a_1269_, 3);
lean_inc_ref(v_arg_1152_);
lean_inc_ref(v_e_x27_1261_);
v___x_1272_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1261_, v_arg_1152_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
lean_inc_ref(v_binderType_1270_);
v___x_1274_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1270_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
lean_inc_ref(v_body_1271_);
v___x_1276_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1271_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1296_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1296_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1296_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___y_1288_; 
v___x_1281_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_a_1277_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1275_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_mkConst(v___x_1281_, v___x_1284_);
lean_inc_ref(v_body_1271_);
v___x_1286_ = l_Lean_mkApp6(v___x_1285_, v_binderType_1270_, v_body_1271_, v_fn_1151_, v_e_x27_1261_, v_proof_1262_, v_arg_1152_);
if (v_contextDependent_1263_ == 0)
{
v___y_1288_ = v_contextDependent_1267_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___x_1153_;
goto v___jp_1287_;
}
v___jp_1287_:
{
lean_object* v___x_1290_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v___x_1286_);
lean_ctor_set(v___x_1265_, 0, v_a_1273_);
v___x_1290_ = v___x_1265_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1273_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1286_);
v___x_1290_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*2, v___x_1150_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*2 + 1, v___y_1288_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_body_1271_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1291_);
v___x_1293_ = v___x_1279_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_a_1275_);
lean_dec(v_a_1273_);
lean_dec_ref(v_body_1271_);
lean_dec_ref(v_binderType_1270_);
lean_del_object(v___x_1265_);
lean_dec_ref(v_proof_1262_);
lean_dec_ref(v_e_x27_1261_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1297_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1276_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1276_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_a_1273_);
lean_dec_ref(v_body_1271_);
lean_dec_ref(v_binderType_1270_);
lean_del_object(v___x_1265_);
lean_dec_ref(v_proof_1262_);
lean_dec_ref(v_e_x27_1261_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1305_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1274_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1274_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_body_1271_);
lean_dec_ref(v_binderType_1270_);
lean_del_object(v___x_1265_);
lean_dec_ref(v_proof_1262_);
lean_dec_ref(v_e_x27_1261_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1313_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1272_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1272_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_a_1269_);
lean_del_object(v___x_1265_);
lean_dec_ref(v_proof_1262_);
lean_dec_ref(v_e_x27_1261_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1322_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1321_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1322_;
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_del_object(v___x_1265_);
lean_dec_ref(v_proof_1262_);
lean_dec_ref(v_e_x27_1261_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1323_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1268_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1268_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1332_; lean_object* v_proof_1333_; uint8_t v_contextDependent_1334_; lean_object* v_e_x27_1335_; lean_object* v_proof_1336_; uint8_t v_contextDependent_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1404_; 
v_e_x27_1332_ = lean_ctor_get(v_fst_1158_, 0);
lean_inc_ref(v_e_x27_1332_);
v_proof_1333_ = lean_ctor_get(v_fst_1158_, 1);
lean_inc_ref(v_proof_1333_);
v_contextDependent_1334_ = lean_ctor_get_uint8(v_fst_1158_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1158_, 2);
v_e_x27_1335_ = lean_ctor_get(v_a_1164_, 0);
v_proof_1336_ = lean_ctor_get(v_a_1164_, 1);
v_contextDependent_1337_ = lean_ctor_get_uint8(v_a_1164_, sizeof(void*)*2 + 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1339_ = v_a_1164_;
v_isShared_1340_ = v_isSharedCheck_1404_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_proof_1336_);
lean_inc(v_e_x27_1335_);
lean_dec(v_a_1164_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1404_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1159_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
if (lean_obj_tag(v_a_1342_) == 7)
{
lean_object* v_binderType_1343_; lean_object* v_body_1344_; lean_object* v___x_1345_; 
v_binderType_1343_ = lean_ctor_get(v_a_1342_, 1);
lean_inc_ref(v_binderType_1343_);
v_body_1344_ = lean_ctor_get(v_a_1342_, 2);
lean_inc_ref(v_body_1344_);
lean_dec_ref_known(v_a_1342_, 3);
lean_inc_ref(v_e_x27_1335_);
lean_inc_ref(v_e_x27_1332_);
v___x_1345_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1332_, v_e_x27_1335_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
lean_inc_ref(v_binderType_1343_);
v___x_1347_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1343_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
lean_inc_ref(v_body_1344_);
v___x_1349_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1344_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1369_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1369_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1369_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___y_1361_; 
v___x_1354_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_a_1350_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1348_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_mkConst(v___x_1354_, v___x_1357_);
lean_inc_ref(v_body_1344_);
v___x_1359_ = l_Lean_mkApp8(v___x_1358_, v_binderType_1343_, v_body_1344_, v_fn_1151_, v_e_x27_1332_, v_arg_1152_, v_e_x27_1335_, v_proof_1333_, v_proof_1336_);
if (v_contextDependent_1334_ == 0)
{
v___y_1361_ = v_contextDependent_1337_;
goto v___jp_1360_;
}
else
{
v___y_1361_ = v___x_1153_;
goto v___jp_1360_;
}
v___jp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1359_);
lean_ctor_set(v___x_1339_, 0, v_a_1346_);
v___x_1363_ = v___x_1339_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1346_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1359_);
v___x_1363_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*2, v___x_1150_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*2 + 1, v___y_1361_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_body_1344_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1364_);
v___x_1366_ = v___x_1352_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1348_);
lean_dec(v_a_1346_);
lean_dec_ref(v_body_1344_);
lean_dec_ref(v_binderType_1343_);
lean_del_object(v___x_1339_);
lean_dec_ref(v_proof_1336_);
lean_dec_ref(v_e_x27_1335_);
lean_dec_ref(v_proof_1333_);
lean_dec_ref(v_e_x27_1332_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1370_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1349_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1349_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_a_1346_);
lean_dec_ref(v_body_1344_);
lean_dec_ref(v_binderType_1343_);
lean_del_object(v___x_1339_);
lean_dec_ref(v_proof_1336_);
lean_dec_ref(v_e_x27_1335_);
lean_dec_ref(v_proof_1333_);
lean_dec_ref(v_e_x27_1332_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1378_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1347_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1347_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_body_1344_);
lean_dec_ref(v_binderType_1343_);
lean_del_object(v___x_1339_);
lean_dec_ref(v_proof_1336_);
lean_dec_ref(v_e_x27_1335_);
lean_dec_ref(v_proof_1333_);
lean_dec_ref(v_e_x27_1332_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1386_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1345_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1345_);
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
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec(v_a_1342_);
lean_del_object(v___x_1339_);
lean_dec_ref(v_proof_1336_);
lean_dec_ref(v_e_x27_1335_);
lean_dec_ref(v_proof_1333_);
lean_dec_ref(v_e_x27_1332_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v___x_1394_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1395_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1394_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1395_;
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1339_);
lean_dec_ref(v_proof_1336_);
lean_dec_ref(v_e_x27_1335_);
lean_dec_ref(v_proof_1333_);
lean_dec_ref(v_e_x27_1332_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1396_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1341_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1341_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
v___jp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1169_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1171_);
lean_ctor_set(v___x_1161_, 0, v___x_1170_);
v___x_1173_ = v___x_1161_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1173_);
v___x_1175_ = v___x_1166_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
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
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1161_);
lean_dec(v_snd_1159_);
lean_dec(v_fst_1158_);
lean_dec(v___x_1155_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
v_a_1406_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1163_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1163_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_dec(v___x_1155_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_fn_1151_);
return v___x_1156_;
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_e_1138_);
v___x_1415_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1416_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1415_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1416_;
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_e_1138_);
v___x_1417_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1419_, lean_object* v_e_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1419_, v_e_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec(v_i_1419_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1432_, lean_object* v_e_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1432_, v_e_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_fst_1449_; lean_object* v___x_1451_; 
v_fst_1449_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_fst_1449_);
lean_dec(v_a_1445_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v_fst_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_fst_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_a_1454_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1444_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1444_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1462_, lean_object* v_e_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1462_, v_e_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec(v_n_1462_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1475_, lean_object* v_prefixSize_1476_, lean_object* v_suffixSize_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_numArgs_1488_; uint8_t v___x_1489_; 
v_numArgs_1488_ = l_Lean_Expr_getAppNumArgs(v_e_1475_);
v___x_1489_ = lean_nat_dec_le(v_numArgs_1488_, v_prefixSize_1476_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = lean_nat_add(v_prefixSize_1476_, v_suffixSize_1477_);
v___x_1491_ = lean_nat_dec_lt(v___x_1490_, v_numArgs_1488_);
lean_dec(v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_suffixSize_1477_);
v___x_1492_ = lean_nat_sub(v_numArgs_1488_, v_prefixSize_1476_);
lean_dec(v_numArgs_1488_);
v___x_1493_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1492_, v_e_1475_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v___x_1492_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = lean_nat_sub(v_numArgs_1488_, v_prefixSize_1476_);
lean_dec(v_numArgs_1488_);
v___x_1495_ = lean_nat_sub(v___x_1494_, v_suffixSize_1477_);
lean_dec(v___x_1494_);
v___x_1496_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1496_, 0, v_suffixSize_1477_);
v___x_1497_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1496_, v_e_1475_, v___x_1495_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v___x_1495_);
return v___x_1497_;
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v_numArgs_1488_);
lean_dec(v_suffixSize_1477_);
lean_dec_ref(v_e_1475_);
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1500_, lean_object* v_prefixSize_1501_, lean_object* v_suffixSize_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1500_, v_prefixSize_1501_, v_suffixSize_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec(v_prefixSize_1501_);
return v_res_1513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1516_ = lean_unsigned_to_nat(13u);
v___x_1517_ = lean_unsigned_to_nat(324u);
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1519_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1520_ = l_mkPanicMessageWithDecl(v___x_1519_, v___x_1518_, v___x_1517_, v___x_1516_, v___x_1515_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1521_, lean_object* v_i_1522_, lean_object* v_e_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_nat_dec_eq(v_i_1522_, v___x_1534_);
if (v___x_1535_ == 0)
{
if (lean_obj_tag(v_e_1523_) == 5)
{
lean_object* v_fn_1536_; lean_object* v_arg_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_fn_1536_ = lean_ctor_get(v_e_1523_, 0);
lean_inc_ref_n(v_fn_1536_, 2);
v_arg_1537_ = lean_ctor_get(v_e_1523_, 1);
lean_inc_ref(v_arg_1537_);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_sub(v_i_1522_, v___x_1538_);
v___x_1540_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1521_, v___x_1539_, v_fn_1536_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1560_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1560_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1560_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = lean_array_fget_borrowed(v_rewritable_1521_, v___x_1539_);
lean_dec(v___x_1539_);
v___x_1546_ = lean_unbox(v___x_1545_);
if (v___x_1546_ == 0)
{
if (lean_obj_tag(v_a_1541_) == 0)
{
uint8_t v_contextDependent_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_dec_ref(v_arg_1537_);
lean_dec_ref_known(v_e_1523_, 2);
lean_dec_ref(v_fn_1536_);
v_contextDependent_1547_ = lean_ctor_get_uint8(v_a_1541_, 1);
lean_dec_ref_known(v_a_1541_, 0);
v___x_1548_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1547_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1548_);
v___x_1550_ = v___x_1543_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
else
{
lean_object* v_e_x27_1552_; lean_object* v_proof_1553_; uint8_t v_contextDependent_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
lean_del_object(v___x_1543_);
v_e_x27_1552_ = lean_ctor_get(v_a_1541_, 0);
lean_inc_ref(v_e_x27_1552_);
v_proof_1553_ = lean_ctor_get(v_a_1541_, 1);
lean_inc_ref(v_proof_1553_);
v_contextDependent_1554_ = lean_ctor_get_uint8(v_a_1541_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1541_, 2);
v___x_1555_ = lean_unbox(v___x_1545_);
v___x_1556_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1523_, v_fn_1536_, v_arg_1537_, v_e_x27_1552_, v_proof_1553_, v___x_1555_, v_contextDependent_1554_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1556_;
}
}
else
{
lean_object* v___x_1557_; 
lean_del_object(v___x_1543_);
lean_inc(v_a_1532_);
lean_inc_ref(v_a_1531_);
lean_inc(v_a_1530_);
lean_inc_ref(v_a_1529_);
lean_inc(v_a_1528_);
lean_inc_ref(v_a_1527_);
lean_inc(v_a_1526_);
lean_inc_ref(v_a_1525_);
lean_inc(v_a_1524_);
lean_inc_ref(v_arg_1537_);
v___x_1557_ = lean_sym_simp(v_arg_1537_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1523_, v_fn_1536_, v_arg_1537_, v_a_1541_, v_a_1558_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1559_;
}
else
{
lean_dec(v_a_1541_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref_known(v_e_1523_, 2);
lean_dec_ref(v_fn_1536_);
return v___x_1557_;
}
}
}
}
else
{
lean_dec(v___x_1539_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref_known(v_e_1523_, 2);
lean_dec_ref(v_fn_1536_);
return v___x_1540_;
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_e_1523_);
v___x_1561_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1562_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1561_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1562_;
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_e_1523_);
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1565_, lean_object* v_i_1566_, lean_object* v_e_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1565_, v_i_1566_, v_e_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec(v_i_1566_);
lean_dec_ref(v_rewritable_1565_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1579_, lean_object* v_i_1580_, lean_object* v_e_1581_, lean_object* v_h_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1579_, v_i_1580_, v_e_1581_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1594_, lean_object* v_i_1595_, lean_object* v_e_1596_, lean_object* v_h_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1594_, v_i_1595_, v_e_1596_, v_h_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec(v_i_1595_);
lean_dec_ref(v_rewritable_1594_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1609_, lean_object* v___x_1610_, lean_object* v_x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1609_, v___x_1610_, v_x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1623_, lean_object* v___x_1624_, lean_object* v_x_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1623_, v___x_1624_, v_x_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v___x_1624_);
lean_dec_ref(v_rewritable_1623_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1637_, lean_object* v_rewritable_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_numArgs_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_numArgs_1649_ = l_Lean_Expr_getAppNumArgs(v_e_1637_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = lean_nat_dec_eq(v_numArgs_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = lean_array_get_size(v_rewritable_1638_);
v___x_1653_ = lean_nat_dec_lt(v___x_1652_, v_numArgs_1649_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1638_, v_numArgs_1649_, v_e_1637_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v_numArgs_1649_);
lean_dec_ref(v_rewritable_1638_);
return v___x_1654_;
}
else
{
lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1655_, 0, v_rewritable_1638_);
lean_closure_set(v___f_1655_, 1, v___x_1652_);
v___x_1656_ = lean_nat_sub(v_numArgs_1649_, v___x_1652_);
lean_dec(v_numArgs_1649_);
v___x_1657_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1655_, v_e_1637_, v___x_1656_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v___x_1656_);
return v___x_1657_;
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_numArgs_1649_);
lean_dec_ref(v_rewritable_1638_);
lean_dec_ref(v_e_1637_);
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1660_, lean_object* v_rewritable_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1660_, v_rewritable_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1673_, lean_object* v_numEqs_1674_, lean_object* v_result_1675_){
_start:
{
if (lean_obj_tag(v_result_1675_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
lean_dec(v_numEqs_1674_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_array_get_size(v_argResults_1673_);
v___x_1678_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_dec_ref_known(v_result_1675_, 0);
return v_argResults_1673_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_array_push(v_argResults_1673_, v_result_1675_);
return v___x_1679_;
}
}
else
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = lean_array_get_size(v_argResults_1673_);
v___x_1681_ = lean_nat_dec_lt(v___x_1680_, v_numEqs_1674_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec(v_numEqs_1674_);
v___x_1682_ = lean_array_push(v_argResults_1673_, v_result_1675_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v_argResults_1673_);
v___x_1683_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1684_ = lean_mk_array(v_numEqs_1674_, v___x_1683_);
v___x_1685_ = lean_array_push(v___x_1684_, v_result_1675_);
return v___x_1685_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1688_ = lean_unsigned_to_nat(13u);
v___x_1689_ = lean_unsigned_to_nat(445u);
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1692_ = l_mkPanicMessageWithDecl(v___x_1691_, v___x_1690_, v___x_1689_, v___x_1688_, v___x_1687_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1693_, lean_object* v_mkNonRflResult_1694_, lean_object* v_e_1695_, lean_object* v_i_1696_, lean_object* v_numEqs_1697_, lean_object* v_argResults_1698_, uint8_t v_anyCD_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
if (lean_obj_tag(v_e_1695_) == 5)
{
lean_object* v_fn_1710_; lean_object* v_arg_1711_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_fn_1710_ = lean_ctor_get(v_e_1695_, 0);
lean_inc_ref(v_fn_1710_);
v_arg_1711_ = lean_ctor_get(v_e_1695_, 1);
lean_inc_ref(v_arg_1711_);
lean_dec_ref_known(v_e_1695_, 2);
v___x_1725_ = 0;
v___x_1726_ = lean_box(v___x_1725_);
v___x_1727_ = lean_array_get(v___x_1726_, v_argKinds_1693_, v_i_1696_);
lean_dec(v___x_1726_);
v___x_1728_ = lean_unbox(v___x_1727_);
lean_dec(v___x_1727_);
switch(v___x_1728_)
{
case 5:
{
lean_dec_ref(v_arg_1711_);
v___y_1713_ = v_a_1700_;
v___y_1714_ = v_a_1701_;
v___y_1715_ = v_a_1702_;
v___y_1716_ = v_a_1703_;
v___y_1717_ = v_a_1704_;
v___y_1718_ = v_a_1705_;
v___y_1719_ = v_a_1706_;
v___y_1720_ = v_a_1707_;
v___y_1721_ = v_a_1708_;
goto v___jp_1712_;
}
case 0:
{
lean_dec_ref(v_arg_1711_);
v___y_1713_ = v_a_1700_;
v___y_1714_ = v_a_1701_;
v___y_1715_ = v_a_1702_;
v___y_1716_ = v_a_1703_;
v___y_1717_ = v_a_1704_;
v___y_1718_ = v_a_1705_;
v___y_1719_ = v_a_1706_;
v___y_1720_ = v_a_1707_;
v___y_1721_ = v_a_1708_;
goto v___jp_1712_;
}
case 3:
{
lean_dec_ref(v_arg_1711_);
v___y_1713_ = v_a_1700_;
v___y_1714_ = v_a_1701_;
v___y_1715_ = v_a_1702_;
v___y_1716_ = v_a_1703_;
v___y_1717_ = v_a_1704_;
v___y_1718_ = v_a_1705_;
v___y_1719_ = v_a_1706_;
v___y_1720_ = v_a_1707_;
v___y_1721_ = v_a_1708_;
goto v___jp_1712_;
}
case 2:
{
lean_object* v___x_1729_; 
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
lean_inc_ref(v_a_1703_);
lean_inc(v_a_1702_);
lean_inc_ref(v_a_1701_);
lean_inc(v_a_1700_);
v___x_1729_ = lean_sym_simp(v_arg_1711_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_n(v_a_1730_, 2);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_sub(v_i_1696_, v___x_1731_);
lean_dec(v_i_1696_);
v___x_1733_ = lean_nat_add(v_numEqs_1697_, v___x_1731_);
v___x_1734_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1698_, v_numEqs_1697_, v_a_1730_);
if (v_anyCD_1699_ == 0)
{
if (lean_obj_tag(v_a_1730_) == 0)
{
uint8_t v_contextDependent_1735_; 
v_contextDependent_1735_ = lean_ctor_get_uint8(v_a_1730_, 1);
lean_dec_ref_known(v_a_1730_, 0);
v_e_1695_ = v_fn_1710_;
v_i_1696_ = v___x_1732_;
v_numEqs_1697_ = v___x_1733_;
v_argResults_1698_ = v___x_1734_;
v_anyCD_1699_ = v_contextDependent_1735_;
goto _start;
}
else
{
uint8_t v_contextDependent_1737_; 
v_contextDependent_1737_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1730_, 2);
v_e_1695_ = v_fn_1710_;
v_i_1696_ = v___x_1732_;
v_numEqs_1697_ = v___x_1733_;
v_argResults_1698_ = v___x_1734_;
v_anyCD_1699_ = v_contextDependent_1737_;
goto _start;
}
}
else
{
lean_dec(v_a_1730_);
v_e_1695_ = v_fn_1710_;
v_i_1696_ = v___x_1732_;
v_numEqs_1697_ = v___x_1733_;
v_argResults_1698_ = v___x_1734_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_1710_);
lean_dec_ref(v_argResults_1698_);
lean_dec(v_numEqs_1697_);
lean_dec(v_i_1696_);
lean_dec_ref(v_mkNonRflResult_1694_);
return v___x_1729_;
}
}
default: 
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec_ref(v_arg_1711_);
lean_dec_ref(v_fn_1710_);
lean_dec_ref(v_argResults_1698_);
lean_dec(v_numEqs_1697_);
lean_dec(v_i_1696_);
lean_dec_ref(v_mkNonRflResult_1694_);
v___x_1740_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1741_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1740_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
return v___x_1741_;
}
}
v___jp_1712_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_sub(v_i_1696_, v___x_1722_);
lean_dec(v_i_1696_);
v_e_1695_ = v_fn_1710_;
v_i_1696_ = v___x_1723_;
v_a_1700_ = v___y_1713_;
v_a_1701_ = v___y_1714_;
v_a_1702_ = v___y_1715_;
v_a_1703_ = v___y_1716_;
v_a_1704_ = v___y_1717_;
v_a_1705_ = v___y_1718_;
v_a_1706_ = v___y_1719_;
v_a_1707_ = v___y_1720_;
v_a_1708_ = v___y_1721_;
goto _start;
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
lean_dec(v_numEqs_1697_);
lean_dec(v_i_1696_);
lean_dec_ref(v_e_1695_);
v___x_1742_ = lean_array_get_size(v_argResults_1698_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_nat_dec_eq(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = l_Array_reverse___redArg(v_argResults_1698_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
lean_inc_ref(v_a_1703_);
lean_inc(v_a_1702_);
lean_inc_ref(v_a_1701_);
lean_inc(v_a_1700_);
v___x_1746_ = lean_apply_11(v_mkNonRflResult_1694_, v___x_1745_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
if (v_anyCD_1699_ == 0)
{
lean_dec(v_a_1747_);
return v___x_1746_;
}
else
{
if (lean_obj_tag(v_a_1747_) == 0)
{
uint8_t v_contextDependent_1751_; 
v_contextDependent_1751_ = lean_ctor_get_uint8(v_a_1747_, 1);
if (v_contextDependent_1751_ == 0)
{
lean_dec_ref_known(v___x_1746_, 1);
goto v___jp_1748_;
}
else
{
lean_dec_ref_known(v_a_1747_, 0);
return v___x_1746_;
}
}
else
{
uint8_t v_contextDependent_1752_; 
v_contextDependent_1752_ = lean_ctor_get_uint8(v_a_1747_, sizeof(void*)*2 + 1);
if (v_contextDependent_1752_ == 0)
{
lean_dec_ref_known(v___x_1746_, 1);
goto v___jp_1748_;
}
else
{
lean_dec_ref_known(v_a_1747_, 2);
return v___x_1746_;
}
}
}
v___jp_1748_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1747_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
else
{
return v___x_1746_;
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v_argResults_1698_);
lean_dec_ref(v_mkNonRflResult_1694_);
v___x_1753_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_1699_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object** _args){
lean_object* v_argKinds_1755_ = _args[0];
lean_object* v_mkNonRflResult_1756_ = _args[1];
lean_object* v_e_1757_ = _args[2];
lean_object* v_i_1758_ = _args[3];
lean_object* v_numEqs_1759_ = _args[4];
lean_object* v_argResults_1760_ = _args[5];
lean_object* v_anyCD_1761_ = _args[6];
lean_object* v_a_1762_ = _args[7];
lean_object* v_a_1763_ = _args[8];
lean_object* v_a_1764_ = _args[9];
lean_object* v_a_1765_ = _args[10];
lean_object* v_a_1766_ = _args[11];
lean_object* v_a_1767_ = _args[12];
lean_object* v_a_1768_ = _args[13];
lean_object* v_a_1769_ = _args[14];
lean_object* v_a_1770_ = _args[15];
lean_object* v_a_1771_ = _args[16];
_start:
{
uint8_t v_anyCD_boxed_1772_; lean_object* v_res_1773_; 
v_anyCD_boxed_1772_ = lean_unbox(v_anyCD_1761_);
v_res_1773_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1755_, v_mkNonRflResult_1756_, v_e_1757_, v_i_1758_, v_numEqs_1759_, v_argResults_1760_, v_anyCD_boxed_1772_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_argKinds_1755_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* v_msg_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_17247__overap_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_17247__overap_1786_ = lean_panic_fn_borrowed(v___x_1785_, v_msg_1774_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1778_);
lean_inc(v___y_1777_);
lean_inc_ref(v___y_1776_);
lean_inc(v___y_1775_);
v___x_1787_ = lean_apply_10(v___x_17247__overap_1786_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, lean_box(0));
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
return v_res_1799_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(uint8_t v___x_1800_, lean_object* v_as_1801_, size_t v_i_1802_, size_t v_stop_1803_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = lean_usize_dec_eq(v_i_1802_, v_stop_1803_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_array_uget_borrowed(v_as_1801_, v_i_1802_);
v___x_1810_ = lean_unbox(v___x_1809_);
if (v___x_1810_ == 3)
{
if (v___x_1800_ == 0)
{
goto v___jp_1804_;
}
else
{
return v___x_1800_;
}
}
else
{
goto v___jp_1804_;
}
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = 0;
return v___x_1811_;
}
v___jp_1804_:
{
size_t v___x_1805_; size_t v___x_1806_; 
v___x_1805_ = ((size_t)1ULL);
v___x_1806_ = lean_usize_add(v_i_1802_, v___x_1805_);
v_i_1802_ = v___x_1806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object* v___x_1812_, lean_object* v_as_1813_, lean_object* v_i_1814_, lean_object* v_stop_1815_){
_start:
{
uint8_t v___x_19061__boxed_1816_; size_t v_i_boxed_1817_; size_t v_stop_boxed_1818_; uint8_t v_res_1819_; lean_object* v_r_1820_; 
v___x_19061__boxed_1816_ = lean_unbox(v___x_1812_);
v_i_boxed_1817_ = lean_unbox_usize(v_i_1814_);
lean_dec(v_i_1814_);
v_stop_boxed_1818_ = lean_unbox_usize(v_stop_1815_);
lean_dec(v_stop_1815_);
v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_19061__boxed_1816_, v_as_1813_, v_i_boxed_1817_, v_stop_boxed_1818_);
lean_dec_ref(v_as_1813_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object* v_as_1821_, size_t v_i_1822_, size_t v_stop_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_eq(v_i_1822_, v_stop_1823_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; uint8_t v___y_1827_; lean_object* v___x_1831_; 
v___x_1825_ = 1;
v___x_1831_ = lean_array_uget_borrowed(v_as_1821_, v_i_1822_);
if (lean_obj_tag(v___x_1831_) == 0)
{
uint8_t v_contextDependent_1832_; 
v_contextDependent_1832_ = lean_ctor_get_uint8(v___x_1831_, 1);
v___y_1827_ = v_contextDependent_1832_;
goto v___jp_1826_;
}
else
{
uint8_t v_contextDependent_1833_; 
v_contextDependent_1833_ = lean_ctor_get_uint8(v___x_1831_, sizeof(void*)*2 + 1);
v___y_1827_ = v_contextDependent_1833_;
goto v___jp_1826_;
}
v___jp_1826_:
{
if (v___y_1827_ == 0)
{
size_t v___x_1828_; size_t v___x_1829_; 
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1822_, v___x_1828_);
v_i_1822_ = v___x_1829_;
goto _start;
}
else
{
return v___x_1825_;
}
}
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = 0;
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v_as_1835_, lean_object* v_i_1836_, lean_object* v_stop_1837_){
_start:
{
size_t v_i_boxed_1838_; size_t v_stop_boxed_1839_; uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_i_boxed_1838_ = lean_unbox_usize(v_i_1836_);
lean_dec(v_i_1836_);
v_stop_boxed_1839_ = lean_unbox_usize(v_stop_1837_);
lean_dec(v_stop_1837_);
v_res_1840_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1835_, v_i_boxed_1838_, v_stop_boxed_1839_);
lean_dec_ref(v_as_1835_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1844_ = lean_unsigned_to_nat(13u);
v___x_1845_ = lean_unsigned_to_nat(417u);
v___x_1846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1847_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1848_ = l_mkPanicMessageWithDecl(v___x_1847_, v___x_1846_, v___x_1845_, v___x_1844_, v___x_1843_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1849_, lean_object* v_as_1850_, size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_a_1865_; uint8_t v___x_1869_; 
v___x_1869_ = lean_usize_dec_lt(v_i_1852_, v_sz_1851_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_b_1853_);
return v___x_1870_;
}
else
{
lean_object* v_snd_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_2066_; 
v_snd_1871_ = lean_ctor_get(v_b_1853_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_b_1853_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v_b_1853_, 0);
lean_dec(v_unused_2067_);
v___x_1873_ = v_b_1853_;
v_isShared_1874_ = v_isSharedCheck_2066_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_snd_1871_);
lean_dec(v_b_1853_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_2066_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_snd_1875_; lean_object* v_snd_1876_; lean_object* v_snd_1877_; lean_object* v_snd_1878_; lean_object* v_fst_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_2064_; 
v_snd_1875_ = lean_ctor_get(v_snd_1871_, 1);
lean_inc(v_snd_1875_);
v_snd_1876_ = lean_ctor_get(v_snd_1875_, 1);
lean_inc(v_snd_1876_);
v_snd_1877_ = lean_ctor_get(v_snd_1876_, 1);
lean_inc(v_snd_1877_);
v_snd_1878_ = lean_ctor_get(v_snd_1877_, 1);
lean_inc(v_snd_1878_);
v_fst_1879_ = lean_ctor_get(v_snd_1871_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_snd_1871_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_snd_1871_, 1);
lean_dec(v_unused_2065_);
v___x_1881_ = v_snd_1871_;
v_isShared_1882_ = v_isSharedCheck_2064_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_fst_1879_);
lean_dec(v_snd_1871_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_2064_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_fst_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_2062_; 
v_fst_1883_ = lean_ctor_get(v_snd_1875_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_snd_1875_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v_snd_1875_, 1);
lean_dec(v_unused_2063_);
v___x_1885_ = v_snd_1875_;
v_isShared_1886_ = v_isSharedCheck_2062_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_fst_1883_);
lean_dec(v_snd_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_2062_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_fst_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_2060_; 
v_fst_1887_ = lean_ctor_get(v_snd_1876_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_snd_1876_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v_snd_1876_, 1);
lean_dec(v_unused_2061_);
v___x_1889_ = v_snd_1876_;
v_isShared_1890_ = v_isSharedCheck_2060_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_fst_1887_);
lean_dec(v_snd_1876_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_2060_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_fst_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_2058_; 
v_fst_1891_ = lean_ctor_get(v_snd_1877_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_snd_1877_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_snd_1877_, 1);
lean_dec(v_unused_2059_);
v___x_1893_ = v_snd_1877_;
v_isShared_1894_ = v_isSharedCheck_2058_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_fst_1891_);
lean_dec(v_snd_1877_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_2058_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_array_1895_; lean_object* v_start_1896_; lean_object* v_stop_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_array_1895_ = lean_ctor_get(v_snd_1878_, 0);
v_start_1896_ = lean_ctor_get(v_snd_1878_, 1);
v_stop_1897_ = lean_ctor_get(v_snd_1878_, 2);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_nat_dec_lt(v_start_1896_, v_stop_1897_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1901_; 
if (v_isShared_1894_ == 0)
{
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_fst_1891_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_snd_1878_);
v___x_1901_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v___x_1901_);
v___x_1903_ = v___x_1889_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_fst_1887_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1903_);
v___x_1905_ = v___x_1885_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_fst_1883_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v___x_1905_);
v___x_1907_ = v___x_1881_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_fst_1879_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1907_);
lean_ctor_set(v___x_1873_, 0, v___x_1898_);
v___x_1909_ = v___x_1873_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
}
}
}
}
}
else
{
lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_2054_; 
lean_inc(v_stop_1897_);
lean_inc(v_start_1896_);
lean_inc_ref(v_array_1895_);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_snd_1878_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2055_ = lean_ctor_get(v_snd_1878_, 2);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_snd_1878_, 1);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_snd_1878_, 0);
lean_dec(v_unused_2057_);
v___x_1917_ = v_snd_1878_;
v_isShared_1918_ = v_isSharedCheck_2054_;
goto v_resetjp_1916_;
}
else
{
lean_dec(v_snd_1878_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_2054_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v_a_1919_ = lean_array_uget_borrowed(v_as_1850_, v_i_1852_);
v___x_1920_ = lean_array_fget(v_array_1895_, v_start_1896_);
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_nat_add(v_start_1896_, v___x_1921_);
lean_dec(v_start_1896_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v___x_1922_);
v___x_1924_ = v___x_1917_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_array_1895_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_stop_1897_);
v___x_1924_ = v_reuseFailAlloc_2053_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_proof_1928_; lean_object* v_subst_1929_; uint8_t v___x_1955_; 
lean_inc(v_a_1919_);
v___x_1925_ = l_Lean_Expr_app___override(v_fst_1879_, v_a_1919_);
v___x_1926_ = l_Lean_Expr_bindingBody_x21(v_fst_1883_);
lean_dec(v_fst_1883_);
v___x_1955_ = lean_unbox(v___x_1920_);
lean_dec(v___x_1920_);
switch(v___x_1955_)
{
case 0:
{
lean_del_object(v___x_1893_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1885_);
lean_del_object(v___x_1881_);
lean_del_object(v___x_1873_);
goto v___jp_1948_;
}
case 3:
{
lean_del_object(v___x_1893_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1885_);
lean_del_object(v___x_1881_);
lean_del_object(v___x_1873_);
goto v___jp_1948_;
}
case 5:
{
lean_object* v___x_1956_; lean_object* v_instNew_1958_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_del_object(v___x_1893_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1885_);
lean_del_object(v___x_1881_);
lean_del_object(v___x_1873_);
lean_inc_n(v_a_1919_, 2);
v___x_1956_ = lean_array_push(v_fst_1891_, v_a_1919_);
v___x_1967_ = l_Lean_Expr_bindingDomain_x21(v___x_1926_);
v___x_1968_ = lean_expr_instantiate_rev(v___x_1967_, v___x_1956_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = l_Lean_Meta_Sym_inferType(v_a_1919_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
lean_inc_ref(v___x_1968_);
v___x_1971_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_1970_, v___x_1968_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; uint8_t v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = lean_unbox(v_a_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Meta_trySynthInstance(v___x_1968_, v___x_1898_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1992_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1992_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1992_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
if (lean_obj_tag(v_a_1975_) == 1)
{
lean_object* v_a_1979_; 
lean_del_object(v___x_1977_);
lean_dec(v_a_1972_);
v_a_1979_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v_a_1975_, 1);
v_instNew_1958_ = v_a_1979_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_1980_; uint8_t v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec(v_a_1975_);
v___x_1980_ = lean_alloc_ctor(0, 0, 2);
v___x_1981_ = lean_unbox(v_a_1972_);
lean_ctor_set_uint8(v___x_1980_, 0, v___x_1981_);
v___x_1982_ = lean_unbox(v_a_1972_);
lean_dec(v_a_1972_);
lean_ctor_set_uint8(v___x_1980_, 1, v___x_1982_);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1980_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1956_);
lean_ctor_set(v___x_1984_, 1, v___x_1924_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_fst_1887_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1926_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1925_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1983_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1988_);
v___x_1990_ = v___x_1977_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_a_1972_);
lean_dec_ref(v___x_1956_);
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
lean_dec_ref(v___x_1924_);
lean_dec(v_fst_1887_);
v_a_1993_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1974_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1974_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_dec(v_a_1972_);
lean_dec_ref(v___x_1968_);
lean_inc(v_a_1919_);
v_instNew_1958_ = v_a_1919_;
goto v___jp_1957_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v___x_1968_);
lean_dec_ref(v___x_1956_);
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
lean_dec_ref(v___x_1924_);
lean_dec(v_fst_1887_);
v_a_2001_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1971_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1971_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v___x_1968_);
lean_dec_ref(v___x_1956_);
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
lean_dec_ref(v___x_1924_);
lean_dec(v_fst_1887_);
v_a_2009_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1969_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1969_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
v___jp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_inc_ref(v_instNew_1958_);
v___x_1959_ = l_Lean_Expr_app___override(v___x_1925_, v_instNew_1958_);
v___x_1960_ = lean_array_push(v___x_1956_, v_instNew_1958_);
v___x_1961_ = l_Lean_Expr_bindingBody_x21(v___x_1926_);
lean_dec_ref(v___x_1926_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1924_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_fst_1887_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1961_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1959_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1898_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v_a_1865_ = v___x_1966_;
goto v___jp_1864_;
}
}
case 2:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1919_);
v___x_2018_ = lean_array_push(v_fst_1891_, v_a_1919_);
v___x_2019_ = lean_array_get_borrowed(v___x_2017_, v_argResults_1849_, v_fst_1887_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2020_; 
lean_inc(v_a_1919_);
v___x_2020_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1919_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_n(v_a_2021_, 2);
lean_dec_ref_known(v___x_2020_, 1);
lean_inc_n(v_a_1919_, 2);
v___x_2022_ = l_Lean_mkAppB(v___x_1925_, v_a_1919_, v_a_2021_);
v___x_2023_ = lean_array_push(v___x_2018_, v_a_1919_);
v___x_2024_ = lean_array_push(v___x_2023_, v_a_2021_);
v_proof_1928_ = v___x_2022_;
v_subst_1929_ = v___x_2024_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
lean_dec_ref(v___x_1924_);
lean_del_object(v___x_1893_);
lean_del_object(v___x_1889_);
lean_dec(v_fst_1887_);
lean_del_object(v___x_1885_);
lean_del_object(v___x_1881_);
lean_del_object(v___x_1873_);
v_a_2025_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2020_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2020_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_e_x27_2033_; lean_object* v_proof_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_e_x27_2033_ = lean_ctor_get(v___x_2019_, 0);
v_proof_2034_ = lean_ctor_get(v___x_2019_, 1);
lean_inc_ref_n(v_proof_2034_, 2);
lean_inc_ref_n(v_e_x27_2033_, 2);
v___x_2035_ = l_Lean_mkAppB(v___x_1925_, v_e_x27_2033_, v_proof_2034_);
v___x_2036_ = lean_array_push(v___x_2018_, v_e_x27_2033_);
v___x_2037_ = lean_array_push(v___x_2036_, v_proof_2034_);
v_proof_1928_ = v___x_2035_;
v_subst_1929_ = v___x_2037_;
goto v___jp_1927_;
}
}
default: 
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_del_object(v___x_1893_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1885_);
lean_del_object(v___x_1881_);
lean_del_object(v___x_1873_);
v___x_2038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
v___x_2039_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_2038_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref_known(v___x_2039_, 1);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_fst_1891_);
lean_ctor_set(v___x_2040_, 1, v___x_1924_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v_fst_1887_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_1926_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_1925_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_1898_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v_a_1865_ = v___x_2044_;
goto v___jp_1864_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
lean_dec_ref(v___x_1924_);
lean_dec(v_fst_1891_);
lean_dec(v_fst_1887_);
v_a_2045_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2039_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2039_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
v___jp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1930_ = l_Lean_Expr_bindingBody_x21(v___x_1926_);
lean_dec_ref(v___x_1926_);
v___x_1931_ = l_Lean_Expr_bindingBody_x21(v___x_1930_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_nat_add(v_fst_1887_, v___x_1921_);
lean_dec(v_fst_1887_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v___x_1924_);
lean_ctor_set(v___x_1893_, 0, v_subst_1929_);
v___x_1934_ = v___x_1893_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_subst_1929_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1924_);
v___x_1934_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v___x_1934_);
lean_ctor_set(v___x_1889_, 0, v___x_1932_);
v___x_1936_ = v___x_1889_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1936_);
lean_ctor_set(v___x_1885_, 0, v___x_1931_);
v___x_1938_ = v___x_1885_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v___x_1938_);
lean_ctor_set(v___x_1881_, 0, v_proof_1928_);
v___x_1940_ = v___x_1881_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_proof_1928_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1940_);
lean_ctor_set(v___x_1873_, 0, v___x_1898_);
v___x_1942_ = v___x_1873_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_a_1865_ = v___x_1942_;
goto v___jp_1864_;
}
}
}
}
}
}
v___jp_1948_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_inc(v_a_1919_);
v___x_1949_ = lean_array_push(v_fst_1891_, v_a_1919_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1924_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_fst_1887_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1926_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1925_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1898_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v_a_1865_ = v___x_1954_;
goto v___jp_1864_;
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
v___jp_1864_:
{
size_t v___x_1866_; size_t v___x_1867_; 
v___x_1866_ = ((size_t)1ULL);
v___x_1867_ = lean_usize_add(v_i_1852_, v___x_1866_);
v_i_1852_ = v___x_1867_;
v_b_1853_ = v_a_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_2068_, lean_object* v_as_2069_, lean_object* v_sz_2070_, lean_object* v_i_2071_, lean_object* v_b_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2070_);
lean_dec(v_sz_2070_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2071_);
lean_dec(v_i_2071_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_2068_, v_as_2069_, v_sz_boxed_2083_, v_i_boxed_2084_, v_b_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v_as_2069_);
lean_dec_ref(v_argResults_2068_);
return v_res_2085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2087_ = lean_unsigned_to_nat(34u);
v___x_2088_ = lean_unsigned_to_nat(418u);
v___x_2089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2091_ = l_mkPanicMessageWithDecl(v___x_2090_, v___x_2089_, v___x_2088_, v___x_2087_, v___x_2086_);
return v___x_2091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2094_; lean_object* v_dummy_2095_; 
v___x_2094_ = lean_box(0);
v_dummy_2095_ = l_Lean_Expr_sort___override(v___x_2094_);
return v_dummy_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_2099_, lean_object* v_argKinds_2100_, lean_object* v_type_2101_, lean_object* v_proof_2102_, lean_object* v_argResults_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_j_2117_; lean_object* v_subst_2118_; lean_object* v_dummy_2119_; lean_object* v_nargs_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_args_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; size_t v_sz_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v_j_2117_ = lean_unsigned_to_nat(0u);
v_subst_2118_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2119_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2120_ = l_Lean_Expr_getAppNumArgs(v_e_2099_);
lean_inc(v_nargs_2120_);
v___x_2121_ = lean_mk_array(v_nargs_2120_, v_dummy_2119_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_sub(v_nargs_2120_, v___x_2122_);
lean_dec(v_nargs_2120_);
v_args_2124_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2099_, v___x_2121_, v___x_2123_);
v___x_2125_ = lean_array_get_size(v_argKinds_2100_);
lean_inc_ref(v_argKinds_2100_);
v___x_2126_ = l_Array_toSubarray___redArg(v_argKinds_2100_, v_j_2117_, v___x_2125_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_subst_2118_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_j_2117_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_type_2101_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_proof_2102_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2127_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v_sz_2133_ = lean_array_size(v_args_2124_);
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_2103_, v_args_2124_, v_sz_2133_, v___x_2134_, v___x_2132_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec_ref(v_args_2124_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2206_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2206_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2206_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_fst_2140_; 
v_fst_2140_ = lean_ctor_get(v_a_2136_, 0);
if (lean_obj_tag(v_fst_2140_) == 0)
{
lean_object* v_snd_2141_; lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___y_2145_; uint8_t v___y_2146_; lean_object* v_rhs_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_snd_2141_ = lean_ctor_get(v_a_2136_, 1);
lean_inc(v_snd_2141_);
lean_dec(v_a_2136_);
v_fst_2142_ = lean_ctor_get(v_snd_2141_, 0);
lean_inc(v_fst_2142_);
v_snd_2143_ = lean_ctor_get(v_snd_2141_, 1);
lean_inc(v_snd_2143_);
lean_dec(v_snd_2141_);
v_fst_2174_ = lean_ctor_get(v_snd_2143_, 0);
lean_inc(v_fst_2174_);
v_snd_2175_ = lean_ctor_get(v_snd_2143_, 1);
lean_inc(v_snd_2175_);
lean_dec(v_snd_2143_);
v___x_2176_ = l_Lean_Expr_cleanupAnnotations(v_fst_2174_);
v___x_2177_ = l_Lean_Expr_isApp(v___x_2176_);
if (v___x_2177_ == 0)
{
lean_dec_ref(v___x_2176_);
lean_dec(v_snd_2175_);
lean_dec(v_fst_2142_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_argKinds_2100_);
goto v___jp_2114_;
}
else
{
lean_object* v_arg_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_arg_2178_ = lean_ctor_get(v___x_2176_, 1);
lean_inc_ref(v_arg_2178_);
v___x_2179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2176_);
v___x_2180_ = l_Lean_Expr_isApp(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v___x_2179_);
lean_dec_ref(v_arg_2178_);
lean_dec(v_snd_2175_);
lean_dec(v_fst_2142_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_argKinds_2100_);
goto v___jp_2114_;
}
else
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2179_);
v___x_2182_ = l_Lean_Expr_isApp(v___x_2181_);
if (v___x_2182_ == 0)
{
lean_dec_ref(v___x_2181_);
lean_dec_ref(v_arg_2178_);
lean_dec(v_snd_2175_);
lean_dec(v_fst_2142_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_argKinds_2100_);
goto v___jp_2114_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2181_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2185_ = l_Lean_Expr_isConstOf(v___x_2183_, v___x_2184_);
lean_dec_ref(v___x_2183_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v_arg_2178_);
lean_dec(v_snd_2175_);
lean_dec(v_fst_2142_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_argKinds_2100_);
goto v___jp_2114_;
}
else
{
lean_object* v_snd_2186_; lean_object* v_fst_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_snd_2186_ = lean_ctor_get(v_snd_2175_, 1);
lean_inc(v_snd_2186_);
lean_dec(v_snd_2175_);
v_fst_2187_ = lean_ctor_get(v_snd_2186_, 0);
lean_inc(v_fst_2187_);
lean_dec(v_snd_2186_);
v___x_2188_ = lean_expr_instantiate_rev(v_arg_2178_, v_fst_2187_);
lean_dec(v_fst_2187_);
lean_dec_ref(v_arg_2178_);
v___x_2189_ = lean_nat_dec_lt(v_j_2117_, v___x_2125_);
if (v___x_2189_ == 0)
{
lean_dec_ref(v_argKinds_2100_);
v_rhs_2153_ = v___x_2188_;
v___y_2154_ = v___y_2107_;
v___y_2155_ = v___y_2108_;
v___y_2156_ = v___y_2109_;
v___y_2157_ = v___y_2110_;
v___y_2158_ = v___y_2111_;
v___y_2159_ = v___y_2112_;
goto v___jp_2152_;
}
else
{
if (v___x_2189_ == 0)
{
lean_dec_ref(v_argKinds_2100_);
v_rhs_2153_ = v___x_2188_;
v___y_2154_ = v___y_2107_;
v___y_2155_ = v___y_2108_;
v___y_2156_ = v___y_2109_;
v___y_2157_ = v___y_2110_;
v___y_2158_ = v___y_2111_;
v___y_2159_ = v___y_2112_;
goto v___jp_2152_;
}
else
{
size_t v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = lean_usize_of_nat(v___x_2125_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_2185_, v_argKinds_2100_, v___x_2134_, v___x_2190_);
lean_dec_ref(v_argKinds_2100_);
if (v___x_2191_ == 0)
{
v_rhs_2153_ = v___x_2188_;
v___y_2154_ = v___y_2107_;
v___y_2155_ = v___y_2108_;
v___y_2156_ = v___y_2109_;
v___y_2157_ = v___y_2110_;
v___y_2158_ = v___y_2111_;
v___y_2159_ = v___y_2112_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2188_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v_rhs_2153_ = v_a_2193_;
v___y_2154_ = v___y_2107_;
v___y_2155_ = v___y_2108_;
v___y_2156_ = v___y_2109_;
v___y_2157_ = v___y_2110_;
v___y_2158_ = v___y_2111_;
v___y_2159_ = v___y_2112_;
goto v___jp_2152_;
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_fst_2142_);
lean_del_object(v___x_2138_);
v_a_2194_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2192_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
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
v___jp_2144_:
{
uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2147_ = 0;
v___x_2148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2148_, 0, v___y_2145_);
lean_ctor_set(v___x_2148_, 1, v_fst_2142_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2, v___x_2147_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2 + 1, v___y_2146_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2148_);
v___x_2150_ = v___x_2138_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
v___jp_2152_:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Meta_Sym_shareCommonInc(v_rhs_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_array_get_size(v_argResults_2103_);
v___x_2163_ = lean_nat_dec_lt(v_j_2117_, v___x_2162_);
if (v___x_2163_ == 0)
{
v___y_2145_ = v_a_2161_;
v___y_2146_ = v___x_2163_;
goto v___jp_2144_;
}
else
{
if (v___x_2163_ == 0)
{
v___y_2145_ = v_a_2161_;
v___y_2146_ = v___x_2163_;
goto v___jp_2144_;
}
else
{
size_t v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_usize_of_nat(v___x_2162_);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_2103_, v___x_2134_, v___x_2164_);
v___y_2145_ = v_a_2161_;
v___y_2146_ = v___x_2165_;
goto v___jp_2144_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_fst_2142_);
lean_del_object(v___x_2138_);
v_a_2166_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2160_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2160_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
else
{
lean_object* v_val_2202_; lean_object* v___x_2204_; 
lean_inc_ref(v_fst_2140_);
lean_dec(v_a_2136_);
lean_dec_ref(v_argKinds_2100_);
v_val_2202_ = lean_ctor_get(v_fst_2140_, 0);
lean_inc(v_val_2202_);
lean_dec_ref_known(v_fst_2140_, 1);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_val_2202_);
v___x_2204_ = v___x_2138_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_val_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_argKinds_2100_);
v_a_2207_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2135_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2135_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
v___jp_2114_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_2116_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2115_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2215_, lean_object* v_argKinds_2216_, lean_object* v_type_2217_, lean_object* v_proof_2218_, lean_object* v_argResults_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2215_, v_argKinds_2216_, v_type_2217_, v_proof_2218_, v_argResults_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v_argResults_2219_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2243_, 0, v___x_2231_);
lean_ctor_set_uint8(v___x_2243_, 1, v___x_2231_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2245_, lean_object* v_x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
uint8_t v___x_19776__boxed_2257_; lean_object* v_res_2258_; 
v___x_19776__boxed_2257_ = lean_unbox(v___x_2245_);
v_res_2258_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_19776__boxed_2257_, v_x_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v_x_2246_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2261_, lean_object* v_argKinds_2262_, lean_object* v_mkNonRflResult_2263_, lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = lean_nat_sub(v___x_2261_, v___x_2275_);
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2279_ = 0;
v___x_2280_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2262_, v_mkNonRflResult_2263_, v_x_2264_, v___x_2276_, v___x_2277_, v___x_2278_, v___x_2279_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2281_, lean_object* v_argKinds_2282_, lean_object* v_mkNonRflResult_2283_, lean_object* v_x_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2281_, v_argKinds_2282_, v_mkNonRflResult_2283_, v_x_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v_argKinds_2282_);
lean_dec(v___x_2281_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2296_, lean_object* v_thm_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_type_2308_; lean_object* v_proof_2309_; lean_object* v_argKinds_2310_; lean_object* v_mkNonRflResult_2311_; lean_object* v_numArgs_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_type_2308_ = lean_ctor_get(v_thm_2297_, 0);
lean_inc_ref(v_type_2308_);
v_proof_2309_ = lean_ctor_get(v_thm_2297_, 1);
lean_inc_ref(v_proof_2309_);
v_argKinds_2310_ = lean_ctor_get(v_thm_2297_, 2);
lean_inc_ref_n(v_argKinds_2310_, 2);
lean_dec_ref(v_thm_2297_);
lean_inc_ref(v_e_2296_);
v_mkNonRflResult_2311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2311_, 0, v_e_2296_);
lean_closure_set(v_mkNonRflResult_2311_, 1, v_argKinds_2310_);
lean_closure_set(v_mkNonRflResult_2311_, 2, v_type_2308_);
lean_closure_set(v_mkNonRflResult_2311_, 3, v_proof_2309_);
v_numArgs_2312_ = l_Lean_Expr_getAppNumArgs(v_e_2296_);
v___x_2313_ = lean_array_get_size(v_argKinds_2310_);
v___x_2314_ = lean_nat_dec_lt(v___x_2313_, v_numArgs_2312_);
if (v___x_2314_ == 0)
{
uint8_t v___x_2315_; 
v___x_2315_ = lean_nat_dec_lt(v_numArgs_2312_, v___x_2313_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec(v_numArgs_2312_);
v___x_2316_ = lean_unsigned_to_nat(1u);
v___x_2317_ = lean_nat_sub(v___x_2313_, v___x_2316_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2320_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2310_, v_mkNonRflResult_2311_, v_e_2296_, v___x_2317_, v___x_2318_, v___x_2319_, v___x_2315_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec_ref(v_argKinds_2310_);
return v___x_2320_;
}
else
{
lean_object* v___x_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_mkNonRflResult_2311_);
lean_dec_ref(v_argKinds_2310_);
v___x_2321_ = lean_box(v___x_2314_);
v___f_2322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2322_, 0, v___x_2321_);
v___x_2323_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2322_, v_e_2296_, v_numArgs_2312_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_numArgs_2312_);
return v___x_2323_;
}
}
else
{
lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___f_2324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2324_, 0, v___x_2313_);
lean_closure_set(v___f_2324_, 1, v_argKinds_2310_);
lean_closure_set(v___f_2324_, 2, v_mkNonRflResult_2311_);
v___x_2325_ = lean_nat_sub(v_numArgs_2312_, v___x_2313_);
lean_dec(v_numArgs_2312_);
v___x_2326_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2324_, v_e_2296_, v___x_2325_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2327_, lean_object* v_thm_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2327_, v_thm_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_f_2351_; lean_object* v___x_2352_; 
v_f_2351_ = l_Lean_Expr_getAppFn(v_e_2340_);
v___x_2352_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2351_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2368_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2368_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2368_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
switch(lean_obj_tag(v_a_2353_))
{
case 0:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_dec_ref(v_e_2340_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2357_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
case 1:
{
lean_object* v_prefixSize_2361_; lean_object* v_suffixSize_2362_; lean_object* v___x_2363_; 
lean_del_object(v___x_2355_);
v_prefixSize_2361_ = lean_ctor_get(v_a_2353_, 0);
lean_inc(v_prefixSize_2361_);
v_suffixSize_2362_ = lean_ctor_get(v_a_2353_, 1);
lean_inc(v_suffixSize_2362_);
lean_dec_ref_known(v_a_2353_, 2);
v___x_2363_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2340_, v_prefixSize_2361_, v_suffixSize_2362_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec(v_prefixSize_2361_);
return v___x_2363_;
}
case 2:
{
lean_object* v_rewritable_2364_; lean_object* v___x_2365_; 
lean_del_object(v___x_2355_);
v_rewritable_2364_ = lean_ctor_get(v_a_2353_, 0);
lean_inc_ref(v_rewritable_2364_);
lean_dec_ref_known(v_a_2353_, 1);
v___x_2365_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2340_, v_rewritable_2364_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2365_;
}
default: 
{
lean_object* v_thm_2366_; lean_object* v___x_2367_; 
lean_del_object(v___x_2355_);
v_thm_2366_ = lean_ctor_get(v_a_2353_, 0);
lean_inc_ref(v_thm_2366_);
lean_dec_ref_known(v_a_2353_, 1);
v___x_2367_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2340_, v_thm_2366_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_e_2340_);
v_a_2369_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2352_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2352_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
return v_res_2388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2391_ = lean_unsigned_to_nat(55u);
v___x_2392_ = lean_unsigned_to_nat(505u);
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2394_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2395_ = l_mkPanicMessageWithDecl(v___x_2394_, v___x_2393_, v___x_2392_, v___x_2391_, v___x_2390_);
return v___x_2395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2397_ = lean_unsigned_to_nat(11u);
v___x_2398_ = lean_unsigned_to_nat(513u);
v___x_2399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2401_ = l_mkPanicMessageWithDecl(v___x_2400_, v___x_2399_, v___x_2398_, v___x_2397_, v___x_2396_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2402_, lean_object* v_e_2403_, lean_object* v_i_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
uint8_t v_cd_2416_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_nat_dec_eq(v_i_2404_, v___x_2419_);
if (v___x_2420_ == 0)
{
if (lean_obj_tag(v_e_2403_) == 5)
{
lean_object* v_fn_2421_; lean_object* v_arg_2422_; lean_object* v___x_2423_; lean_object* v_i_2424_; lean_object* v___x_2425_; 
v_fn_2421_ = lean_ctor_get(v_e_2403_, 0);
lean_inc_ref_n(v_fn_2421_, 2);
v_arg_2422_ = lean_ctor_get(v_e_2403_, 1);
lean_inc_ref(v_arg_2422_);
v___x_2423_ = lean_unsigned_to_nat(1u);
v_i_2424_ = lean_nat_sub(v_i_2404_, v___x_2423_);
v___x_2425_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2402_, v_fn_2421_, v_i_2424_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; uint8_t v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = lean_nat_dec_lt(v_i_2424_, v_stop_2402_);
lean_dec(v_i_2424_);
if (v___x_2427_ == 0)
{
if (lean_obj_tag(v_a_2426_) == 0)
{
uint8_t v_contextDependent_2428_; 
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
v_contextDependent_2428_ = lean_ctor_get_uint8(v_a_2426_, 1);
lean_dec_ref_known(v_a_2426_, 0);
v_cd_2416_ = v_contextDependent_2428_;
goto v___jp_2415_;
}
else
{
lean_object* v_e_x27_2429_; lean_object* v_proof_2430_; uint8_t v_contextDependent_2431_; lean_object* v___x_2432_; 
v_e_x27_2429_ = lean_ctor_get(v_a_2426_, 0);
lean_inc_ref(v_e_x27_2429_);
v_proof_2430_ = lean_ctor_get(v_a_2426_, 1);
lean_inc_ref(v_proof_2430_);
v_contextDependent_2431_ = lean_ctor_get_uint8(v_a_2426_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2426_, 2);
v___x_2432_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2403_, v_fn_2421_, v_arg_2422_, v_e_x27_2429_, v_proof_2430_, v___x_2420_, v_contextDependent_2431_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2432_;
}
}
else
{
lean_object* v___x_2433_; 
lean_inc_ref(v_fn_2421_);
v___x_2433_ = l_Lean_Meta_Sym_inferType(v_fn_2421_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2435_ = l_Lean_Meta_whnfD(v_a_2434_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
if (lean_obj_tag(v_a_2436_) == 7)
{
lean_object* v_binderType_2437_; lean_object* v_body_2438_; uint8_t v___x_2439_; 
v_binderType_2437_ = lean_ctor_get(v_a_2436_, 1);
lean_inc_ref(v_binderType_2437_);
v_body_2438_ = lean_ctor_get(v_a_2436_, 2);
lean_inc_ref(v_body_2438_);
lean_dec_ref_known(v_a_2436_, 3);
v___x_2439_ = l_Lean_Expr_hasLooseBVars(v_body_2438_);
lean_dec_ref(v_body_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Meta_isProp(v_binderType_2437_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; uint8_t v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = lean_unbox(v_a_2441_);
lean_dec(v_a_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_inc(v_a_2413_);
lean_inc_ref(v_a_2412_);
lean_inc(v_a_2411_);
lean_inc_ref(v_a_2410_);
lean_inc(v_a_2409_);
lean_inc_ref(v_a_2408_);
lean_inc(v_a_2407_);
lean_inc_ref(v_a_2406_);
lean_inc(v_a_2405_);
lean_inc_ref(v_arg_2422_);
v___x_2443_ = lean_sym_simp(v_arg_2422_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2403_, v_fn_2421_, v_arg_2422_, v_a_2426_, v_a_2444_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2445_;
}
else
{
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref_known(v_e_2403_, 2);
lean_dec_ref(v_fn_2421_);
return v___x_2443_;
}
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2446_, 0, v___x_2420_);
lean_ctor_set_uint8(v___x_2446_, 1, v___x_2420_);
v___x_2447_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2403_, v_fn_2421_, v_arg_2422_, v_a_2426_, v___x_2446_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2447_;
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
v_a_2448_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2440_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2440_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_2437_);
if (lean_obj_tag(v_a_2426_) == 0)
{
uint8_t v_contextDependent_2456_; 
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
v_contextDependent_2456_ = lean_ctor_get_uint8(v_a_2426_, 1);
lean_dec_ref_known(v_a_2426_, 0);
v_cd_2416_ = v_contextDependent_2456_;
goto v___jp_2415_;
}
else
{
lean_object* v_e_x27_2457_; lean_object* v_proof_2458_; uint8_t v_contextDependent_2459_; lean_object* v___x_2460_; 
v_e_x27_2457_ = lean_ctor_get(v_a_2426_, 0);
lean_inc_ref(v_e_x27_2457_);
v_proof_2458_ = lean_ctor_get(v_a_2426_, 1);
lean_inc_ref(v_proof_2458_);
v_contextDependent_2459_ = lean_ctor_get_uint8(v_a_2426_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2426_, 2);
v___x_2460_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2403_, v_fn_2421_, v_arg_2422_, v_e_x27_2457_, v_proof_2458_, v___x_2420_, v_contextDependent_2459_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2460_;
}
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec(v_a_2436_);
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
v___x_2461_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2462_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2461_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2462_;
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
v_a_2463_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2435_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2435_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
v_a_2471_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2433_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2433_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
else
{
lean_dec(v_i_2424_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_fn_2421_);
lean_dec_ref_known(v_e_2403_, 2);
return v___x_2425_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref(v_e_2403_);
v___x_2479_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2480_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2479_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2480_;
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec_ref(v_e_2403_);
v___x_2481_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
v___jp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2483_, lean_object* v_e_2484_, lean_object* v_i_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2483_, v_e_2484_, v_i_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec(v_i_2485_);
lean_dec(v_stop_2483_);
return v_res_2496_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2499_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2500_ = lean_unsigned_to_nat(2u);
v___x_2501_ = lean_unsigned_to_nat(488u);
v___x_2502_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2504_ = l_mkPanicMessageWithDecl(v___x_2503_, v___x_2502_, v___x_2501_, v___x_2500_, v___x_2499_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2505_, lean_object* v_start_2506_, lean_object* v_stop_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
uint8_t v___x_2518_; 
v___x_2518_ = lean_nat_dec_lt(v_start_2506_, v_stop_2507_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec_ref(v_e_2505_);
v___x_2519_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2520_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2519_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
return v___x_2520_;
}
else
{
lean_object* v_numArgs_2521_; uint8_t v___x_2522_; 
v_numArgs_2521_ = l_Lean_Expr_getAppNumArgs(v_e_2505_);
v___x_2522_ = lean_nat_dec_lt(v_numArgs_2521_, v_start_2506_);
if (v___x_2522_ == 0)
{
lean_object* v_numArgs_2523_; lean_object* v_stop_2524_; lean_object* v___x_2525_; 
v_numArgs_2523_ = lean_nat_sub(v_numArgs_2521_, v_start_2506_);
lean_dec(v_numArgs_2521_);
v_stop_2524_ = lean_nat_sub(v_stop_2507_, v_start_2506_);
v___x_2525_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2524_, v_e_2505_, v_numArgs_2523_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_numArgs_2523_);
lean_dec(v_stop_2524_);
return v___x_2525_;
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v_numArgs_2521_);
lean_dec_ref(v_e_2505_);
v___x_2526_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2528_, lean_object* v_start_2529_, lean_object* v_stop_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2528_, v_start_2529_, v_stop_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec(v_stop_2530_);
lean_dec(v_start_2529_);
return v_res_2541_;
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
