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
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_1_, v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object* v_f_35_, lean_object* v_a_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_35_, v_a_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_44_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object* v_a_45_, lean_object* v_e_46_, lean_object* v_declName_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Sym_inferType(v_a_45_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v___x_57_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc_n(v_a_56_, 2);
lean_dec_ref_known(v___x_55_, 1);
v___x_57_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_56_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_57_, 1);
v___x_59_ = l_Lean_Meta_Sym_inferType(v_e_46_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_n(v_a_60_, 2);
lean_dec_ref_known(v___x_59_, 1);
v___x_61_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_60_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_74_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_74_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_67_, 0, v_a_62_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v_a_58_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = l_Lean_mkConst(v_declName_47_, v___x_68_);
v___x_70_ = l_Lean_mkAppB(v___x_69_, v_a_56_, v_a_60_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_70_);
v___x_72_ = v___x_64_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_a_60_);
lean_dec(v_a_58_);
lean_dec(v_a_56_);
lean_dec(v_declName_47_);
v_a_75_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_61_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_61_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_dec(v_a_58_);
lean_dec(v_a_56_);
lean_dec(v_declName_47_);
return v___x_59_;
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec(v_a_56_);
lean_dec(v_declName_47_);
lean_dec_ref(v_e_46_);
v_a_83_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_57_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_57_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
else
{
lean_dec(v_declName_47_);
lean_dec_ref(v_e_46_);
return v___x_55_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_45_ = stack[0].m_obj;
lean_object* v_e_46_ = stack[1].m_obj;
lean_object* v_declName_47_ = stack[2].m_obj;
lean_object* v___y_48_ = stack[3].m_obj;
lean_object* v___y_49_ = stack[4].m_obj;
lean_object* v___y_50_ = stack[5].m_obj;
lean_object* v___y_51_ = stack[6].m_obj;
lean_object* v___y_52_ = stack[7].m_obj;
lean_object* v___y_53_ = stack[8].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_45_, v_e_46_, v_declName_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object* v_a_92_, lean_object* v_e_93_, lean_object* v_declName_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_92_, v_e_93_, v_declName_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_102_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object* v_e_112_, lean_object* v_f_113_, lean_object* v_a_114_, lean_object* v_fr_115_, lean_object* v_ar_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
uint8_t v___y_125_; 
if (lean_obj_tag(v_fr_115_) == 0)
{
if (lean_obj_tag(v_ar_116_) == 0)
{
uint8_t v_contextDependent_128_; 
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_contextDependent_128_ = lean_ctor_get_uint8(v_fr_115_, 1);
lean_dec_ref_known(v_fr_115_, 0);
if (v_contextDependent_128_ == 0)
{
uint8_t v_contextDependent_129_; 
v_contextDependent_129_ = lean_ctor_get_uint8(v_ar_116_, 1);
lean_dec_ref_known(v_ar_116_, 0);
v___y_125_ = v_contextDependent_129_;
goto v___jp_124_;
}
else
{
lean_dec_ref_known(v_ar_116_, 0);
v___y_125_ = v_contextDependent_128_;
goto v___jp_124_;
}
}
else
{
uint8_t v_contextDependent_130_; lean_object* v_e_x27_131_; lean_object* v_proof_132_; uint8_t v_contextDependent_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_172_; 
v_contextDependent_130_ = lean_ctor_get_uint8(v_fr_115_, 1);
lean_dec_ref_known(v_fr_115_, 0);
v_e_x27_131_ = lean_ctor_get(v_ar_116_, 0);
v_proof_132_ = lean_ctor_get(v_ar_116_, 1);
v_contextDependent_133_ = lean_ctor_get_uint8(v_ar_116_, sizeof(void*)*2 + 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_ar_116_);
if (v_isSharedCheck_172_ == 0)
{
v___x_135_ = v_ar_116_;
v_isShared_136_ = v_isSharedCheck_172_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_proof_132_);
lean_inc(v_e_x27_131_);
lean_dec(v_ar_116_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_172_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; 
lean_inc_ref(v_e_x27_131_);
lean_inc_ref(v_f_113_);
v___x_137_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_113_, v_e_x27_131_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
lean_inc_ref(v_a_114_);
v___x_140_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_114_, v_e_112_, v___x_139_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_155_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_155_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_155_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_155_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; uint8_t v___x_146_; uint8_t v___y_148_; 
v___x_145_ = l_Lean_mkApp4(v_a_141_, v_a_114_, v_e_x27_131_, v_f_113_, v_proof_132_);
v___x_146_ = 0;
if (v_contextDependent_130_ == 0)
{
v___y_148_ = v_contextDependent_133_;
goto v___jp_147_;
}
else
{
v___y_148_ = v_contextDependent_130_;
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v___x_145_);
lean_ctor_set(v___x_135_, 0, v_a_138_);
v___x_150_ = v___x_135_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_138_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_145_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*2, v___x_146_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*2 + 1, v___y_148_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_150_);
v___x_152_ = v___x_143_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_138_);
lean_del_object(v___x_135_);
lean_dec_ref(v_proof_132_);
lean_dec_ref(v_e_x27_131_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
v_a_156_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_140_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_140_);
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
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_del_object(v___x_135_);
lean_dec_ref(v_proof_132_);
lean_dec_ref(v_e_x27_131_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_a_164_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_137_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_137_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
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
lean_object* v_e_x27_173_; lean_object* v_proof_174_; uint8_t v_contextDependent_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_215_; 
v_e_x27_173_ = lean_ctor_get(v_fr_115_, 0);
v_proof_174_ = lean_ctor_get(v_fr_115_, 1);
v_contextDependent_175_ = lean_ctor_get_uint8(v_fr_115_, sizeof(void*)*2 + 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_fr_115_);
if (v_isSharedCheck_215_ == 0)
{
v___x_177_ = v_fr_115_;
v_isShared_178_ = v_isSharedCheck_215_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_proof_174_);
lean_inc(v_e_x27_173_);
lean_dec(v_fr_115_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_215_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
uint8_t v_contextDependent_179_; lean_object* v___x_180_; 
v_contextDependent_179_ = lean_ctor_get_uint8(v_ar_116_, 1);
lean_dec_ref_known(v_ar_116_, 0);
lean_inc_ref(v_a_114_);
lean_inc_ref(v_e_x27_173_);
v___x_180_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_173_, v_a_114_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
lean_inc_ref(v_a_114_);
v___x_183_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_114_, v_e_112_, v___x_182_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_198_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_198_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_198_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_198_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; uint8_t v___x_189_; uint8_t v___y_191_; 
v___x_188_ = l_Lean_mkApp4(v_a_184_, v_f_113_, v_e_x27_173_, v_proof_174_, v_a_114_);
v___x_189_ = 0;
if (v_contextDependent_175_ == 0)
{
v___y_191_ = v_contextDependent_179_;
goto v___jp_190_;
}
else
{
v___y_191_ = v_contextDependent_175_;
goto v___jp_190_;
}
v___jp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_188_);
lean_ctor_set(v___x_177_, 0, v_a_181_);
v___x_193_ = v___x_177_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_181_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_188_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*2, v___x_189_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*2 + 1, v___y_191_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_193_);
v___x_195_ = v___x_186_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_181_);
lean_del_object(v___x_177_);
lean_dec_ref(v_proof_174_);
lean_dec_ref(v_e_x27_173_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
v_a_199_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_183_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_183_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_del_object(v___x_177_);
lean_dec_ref(v_proof_174_);
lean_dec_ref(v_e_x27_173_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_a_207_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_180_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_180_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
else
{
lean_object* v_e_x27_216_; lean_object* v_proof_217_; uint8_t v_contextDependent_218_; lean_object* v_e_x27_219_; lean_object* v_proof_220_; uint8_t v_contextDependent_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_260_; 
v_e_x27_216_ = lean_ctor_get(v_fr_115_, 0);
lean_inc_ref(v_e_x27_216_);
v_proof_217_ = lean_ctor_get(v_fr_115_, 1);
lean_inc_ref(v_proof_217_);
v_contextDependent_218_ = lean_ctor_get_uint8(v_fr_115_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fr_115_, 2);
v_e_x27_219_ = lean_ctor_get(v_ar_116_, 0);
v_proof_220_ = lean_ctor_get(v_ar_116_, 1);
v_contextDependent_221_ = lean_ctor_get_uint8(v_ar_116_, sizeof(void*)*2 + 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_ar_116_);
if (v_isSharedCheck_260_ == 0)
{
v___x_223_ = v_ar_116_;
v_isShared_224_ = v_isSharedCheck_260_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_proof_220_);
lean_inc(v_e_x27_219_);
lean_dec(v_ar_116_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_260_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; 
lean_inc_ref(v_e_x27_219_);
lean_inc_ref(v_e_x27_216_);
v___x_225_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_e_x27_216_, v_e_x27_219_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
lean_inc_ref(v_a_114_);
v___x_228_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(v_a_114_, v_e_112_, v___x_227_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_243_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; uint8_t v___x_234_; uint8_t v___y_236_; 
v___x_233_ = l_Lean_mkApp6(v_a_229_, v_f_113_, v_e_x27_216_, v_a_114_, v_e_x27_219_, v_proof_217_, v_proof_220_);
v___x_234_ = 0;
if (v_contextDependent_218_ == 0)
{
v___y_236_ = v_contextDependent_221_;
goto v___jp_235_;
}
else
{
v___y_236_ = v_contextDependent_218_;
goto v___jp_235_;
}
v___jp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_233_);
lean_ctor_set(v___x_223_, 0, v_a_226_);
v___x_238_ = v___x_223_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_226_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_233_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*2, v___x_234_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*2 + 1, v___y_236_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_238_);
v___x_240_ = v___x_231_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_a_226_);
lean_del_object(v___x_223_);
lean_dec_ref(v_proof_220_);
lean_dec_ref(v_e_x27_219_);
lean_dec_ref(v_proof_217_);
lean_dec_ref(v_e_x27_216_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
v_a_244_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_228_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_228_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_del_object(v___x_223_);
lean_dec_ref(v_proof_220_);
lean_dec_ref(v_e_x27_219_);
lean_dec_ref(v_proof_217_);
lean_dec_ref(v_e_x27_216_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_f_113_);
lean_dec_ref(v_e_112_);
v_a_252_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_225_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_225_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_125_);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkCongr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_112_ = stack[0].m_obj;
lean_object* v_f_113_ = stack[1].m_obj;
lean_object* v_a_114_ = stack[2].m_obj;
lean_object* v_fr_115_ = stack[3].m_obj;
lean_object* v_ar_116_ = stack[4].m_obj;
lean_object* v_a_117_ = stack[5].m_obj;
lean_object* v_a_118_ = stack[6].m_obj;
lean_object* v_a_119_ = stack[7].m_obj;
lean_object* v_a_120_ = stack[8].m_obj;
lean_object* v_a_121_ = stack[9].m_obj;
lean_object* v_a_122_ = stack[10].m_obj;
lean_object* v_res_261_;
v_res_261_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_112_, v_f_113_, v_a_114_, v_fr_115_, v_ar_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object* v_e_262_, lean_object* v_f_263_, lean_object* v_a_264_, lean_object* v_fr_265_, lean_object* v_ar_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_262_, v_f_263_, v_a_264_, v_fr_265_, v_ar_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_274_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object* v_e_275_, lean_object* v_f_276_, lean_object* v_a_277_, lean_object* v_fr_278_, lean_object* v_ar_279_, lean_object* v_x_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_275_, v_f_276_, v_a_277_, v_fr_278_, v_ar_279_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
return v___x_288_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_275_ = stack[0].m_obj;
lean_object* v_f_276_ = stack[1].m_obj;
lean_object* v_a_277_ = stack[2].m_obj;
lean_object* v_fr_278_ = stack[3].m_obj;
lean_object* v_ar_279_ = stack[4].m_obj;
lean_object* v_a_281_ = stack[6].m_obj;
lean_object* v_a_282_ = stack[7].m_obj;
lean_object* v_a_283_ = stack[8].m_obj;
lean_object* v_a_284_ = stack[9].m_obj;
lean_object* v_a_285_ = stack[10].m_obj;
lean_object* v_a_286_ = stack[11].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Lean_Meta_Sym_Simp_mkCongr(v_e_275_, v_f_276_, v_a_277_, v_fr_278_, v_ar_279_, lean_box(0), v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object* v_e_290_, lean_object* v_f_291_, lean_object* v_a_292_, lean_object* v_fr_293_, lean_object* v_ar_294_, lean_object* v_x_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_Sym_Simp_mkCongr(v_e_290_, v_f_291_, v_a_292_, v_fr_293_, v_ar_294_, v_x_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_303_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(lean_object* v_e_304_, lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_ar_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
if (lean_obj_tag(v_ar_307_) == 0)
{
uint8_t v_contextDependent_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec_ref(v_a_306_);
lean_dec_ref(v_f_305_);
lean_dec_ref(v_e_304_);
v_contextDependent_315_ = lean_ctor_get_uint8(v_ar_307_, 1);
lean_dec_ref_known(v_ar_307_, 0);
v___x_316_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_315_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v_e_x27_318_; lean_object* v_proof_319_; uint8_t v_contextDependent_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_391_; 
v_e_x27_318_ = lean_ctor_get(v_ar_307_, 0);
v_proof_319_ = lean_ctor_get(v_ar_307_, 1);
v_contextDependent_320_ = lean_ctor_get_uint8(v_ar_307_, sizeof(void*)*2 + 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_ar_307_);
if (v_isSharedCheck_391_ == 0)
{
v___x_322_ = v_ar_307_;
v_isShared_323_ = v_isSharedCheck_391_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_proof_319_);
lean_inc(v_e_x27_318_);
lean_dec(v_ar_307_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_391_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; 
lean_inc_ref(v_a_306_);
v___x_324_ = l_Lean_Meta_Sym_inferType(v_a_306_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_n(v_a_325_, 2);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_325_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = l_Lean_Meta_Sym_inferType(v_e_304_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_n(v_a_329_, 2);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_329_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
lean_inc_ref(v_e_x27_318_);
lean_inc_ref(v_f_305_);
v___x_332_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_305_, v_e_x27_318_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_350_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_350_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_350_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_350_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_345_; 
v___x_337_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v_a_331_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v_a_327_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_mkConst(v___x_337_, v___x_340_);
v___x_342_ = l_Lean_mkApp6(v___x_341_, v_a_325_, v_a_329_, v_a_306_, v_e_x27_318_, v_f_305_, v_proof_319_);
v___x_343_ = 0;
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_342_);
lean_ctor_set(v___x_322_, 0, v_a_333_);
v___x_345_ = v___x_322_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_333_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_349_, sizeof(void*)*2 + 1, v_contextDependent_320_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*2, v___x_343_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_345_);
v___x_347_ = v___x_335_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_a_331_);
lean_dec(v_a_329_);
lean_dec(v_a_327_);
lean_dec(v_a_325_);
lean_del_object(v___x_322_);
lean_dec_ref(v_proof_319_);
lean_dec_ref(v_e_x27_318_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_f_305_);
v_a_351_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_332_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_332_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_a_329_);
lean_dec(v_a_327_);
lean_dec(v_a_325_);
lean_del_object(v___x_322_);
lean_dec_ref(v_proof_319_);
lean_dec_ref(v_e_x27_318_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_f_305_);
v_a_359_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_330_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_330_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_a_327_);
lean_dec(v_a_325_);
lean_del_object(v___x_322_);
lean_dec_ref(v_proof_319_);
lean_dec_ref(v_e_x27_318_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_f_305_);
v_a_367_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_328_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_328_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_325_);
lean_del_object(v___x_322_);
lean_dec_ref(v_proof_319_);
lean_dec_ref(v_e_x27_318_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_f_305_);
lean_dec_ref(v_e_304_);
v_a_375_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_326_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_326_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_322_);
lean_dec_ref(v_proof_319_);
lean_dec_ref(v_e_x27_318_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_f_305_);
lean_dec_ref(v_e_304_);
v_a_383_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_324_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_324_);
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
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkCongrArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_304_ = stack[0].m_obj;
lean_object* v_f_305_ = stack[1].m_obj;
lean_object* v_a_306_ = stack[2].m_obj;
lean_object* v_ar_307_ = stack[3].m_obj;
lean_object* v_a_308_ = stack[4].m_obj;
lean_object* v_a_309_ = stack[5].m_obj;
lean_object* v_a_310_ = stack[6].m_obj;
lean_object* v_a_311_ = stack[7].m_obj;
lean_object* v_a_312_ = stack[8].m_obj;
lean_object* v_a_313_ = stack[9].m_obj;
lean_object* v_res_392_;
v_res_392_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_304_, v_f_305_, v_a_306_, v_ar_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg___boxed(lean_object* v_e_393_, lean_object* v_f_394_, lean_object* v_a_395_, lean_object* v_ar_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_393_, v_f_394_, v_a_395_, v_ar_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
return v_res_404_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg(lean_object* v_e_405_, lean_object* v_f_406_, lean_object* v_a_407_, lean_object* v_ar_408_, lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_405_, v_f_406_, v_a_407_, v_ar_408_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
return v___x_417_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkCongrArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_405_ = stack[0].m_obj;
lean_object* v_f_406_ = stack[1].m_obj;
lean_object* v_a_407_ = stack[2].m_obj;
lean_object* v_ar_408_ = stack[3].m_obj;
lean_object* v_a_410_ = stack[5].m_obj;
lean_object* v_a_411_ = stack[6].m_obj;
lean_object* v_a_412_ = stack[7].m_obj;
lean_object* v_a_413_ = stack[8].m_obj;
lean_object* v_a_414_ = stack[9].m_obj;
lean_object* v_a_415_ = stack[10].m_obj;
lean_object* v_res_418_;
v_res_418_ = l_Lean_Meta_Sym_Simp_mkCongrArg(v_e_405_, v_f_406_, v_a_407_, v_ar_408_, lean_box(0), v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___boxed(lean_object* v_e_419_, lean_object* v_f_420_, lean_object* v_a_421_, lean_object* v_ar_422_, lean_object* v_x_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_Sym_Simp_mkCongrArg(v_e_419_, v_f_420_, v_a_421_, v_ar_422_, v_x_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_431_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* v_msgData_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v_env_439_; uint8_t v___x_440_; lean_object* v_env_441_; lean_object* v___x_442_; lean_object* v_toCold_443_; lean_object* v_mctx_444_; lean_object* v_lctx_445_; lean_object* v_options_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_438_ = lean_st_ref_get(v___y_436_);
v_env_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_ref(v_env_439_);
lean_dec(v___x_438_);
v___x_440_ = 0;
v_env_441_ = l_Lean_Environment_setRecordingDeps(v_env_439_, v___x_440_);
v___x_442_ = lean_st_ref_get(v___y_434_);
v_toCold_443_ = lean_ctor_get(v___y_435_, 0);
v_mctx_444_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_mctx_444_);
lean_dec(v___x_442_);
v_lctx_445_ = lean_ctor_get(v___y_433_, 2);
v_options_446_ = lean_ctor_get(v_toCold_443_, 2);
lean_inc_ref(v_options_446_);
lean_inc_ref(v_lctx_445_);
v___x_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_447_, 0, v_env_441_);
lean_ctor_set(v___x_447_, 1, v_mctx_444_);
lean_ctor_set(v___x_447_, 2, v_lctx_445_);
lean_ctor_set(v___x_447_, 3, v_options_446_);
v___x_448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_msgData_432_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_432_ = stack[0].m_obj;
lean_object* v___y_433_ = stack[1].m_obj;
lean_object* v___y_434_ = stack[2].m_obj;
lean_object* v___y_435_ = stack[3].m_obj;
lean_object* v___y_436_ = stack[4].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* v_msgData_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_ref_464_; lean_object* v___x_465_; lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_ref_464_ = lean_ctor_get(v___y_461_, 2);
v___x_465_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msg_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_inc(v_ref_464_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_ref_464_);
lean_ctor_set(v___x_470_, 1, v_a_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 1);
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_458_ = stack[0].m_obj;
lean_object* v___y_459_ = stack[1].m_obj;
lean_object* v___y_460_ = stack[2].m_obj;
lean_object* v___y_461_ = stack[3].m_obj;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* v_msg_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* v_e_489_, lean_object* v_f_490_, lean_object* v_a_491_, lean_object* v_f_x27_492_, lean_object* v_hf_493_, uint8_t v_done_494_, uint8_t v_contextDependent_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_503_; 
lean_inc_ref(v_f_490_);
v___x_503_ = l_Lean_Meta_Sym_inferType(v_f_490_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_Meta_whnfD(v_a_504_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
if (lean_obj_tag(v_a_506_) == 7)
{
lean_object* v_binderName_507_; lean_object* v_body_508_; lean_object* v___x_509_; 
v_binderName_507_ = lean_ctor_get(v_a_506_, 0);
lean_inc(v_binderName_507_);
v_body_508_ = lean_ctor_get(v_a_506_, 2);
lean_inc_ref(v_body_508_);
lean_dec_ref_known(v_a_506_, 3);
lean_inc_ref(v_a_491_);
v___x_509_ = l_Lean_Meta_Sym_inferType(v_a_491_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_n(v_a_510_, 2);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_510_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = l_Lean_Meta_Sym_inferType(v_e_489_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_514_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = 0;
lean_inc(v_a_510_);
v___x_518_ = l_Lean_mkLambda(v_binderName_507_, v___x_517_, v_a_510_, v_body_508_);
lean_inc_ref(v_a_491_);
lean_inc_ref(v_f_x27_492_);
v___x_519_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_x27_492_, v_a_491_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_534_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_534_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_534_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_534_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v_a_516_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_512_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_mkConst(v___x_524_, v___x_527_);
v___x_529_ = l_Lean_mkApp6(v___x_528_, v_a_510_, v___x_518_, v_f_490_, v_f_x27_492_, v_hf_493_, v_a_491_);
v___x_530_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_530_, 0, v_a_520_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*2, v_done_494_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*2 + 1, v_contextDependent_495_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_530_);
v___x_532_ = v___x_522_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v___x_518_);
lean_dec(v_a_516_);
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
v_a_535_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_519_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_519_);
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
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec_ref(v_body_508_);
lean_dec(v_binderName_507_);
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
v_a_543_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_515_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_515_);
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
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec_ref(v_body_508_);
lean_dec(v_binderName_507_);
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
v_a_551_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_513_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_513_);
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
lean_dec(v_a_510_);
lean_dec_ref(v_body_508_);
lean_dec(v_binderName_507_);
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
lean_dec_ref(v_e_489_);
v_a_559_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_511_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_511_);
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
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_body_508_);
lean_dec(v_binderName_507_);
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
lean_dec_ref(v_e_489_);
v_a_567_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_509_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_509_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_a_506_);
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_e_489_);
v___x_575_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
v___x_576_ = l_Lean_indentExpr(v_f_490_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_577_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_578_;
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
lean_dec_ref(v_e_489_);
v_a_579_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_505_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_505_);
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
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_hf_493_);
lean_dec_ref(v_f_x27_492_);
lean_dec_ref(v_a_491_);
lean_dec_ref(v_f_490_);
lean_dec_ref(v_e_489_);
v_a_587_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_503_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_503_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_489_ = stack[0].m_obj;
lean_object* v_f_490_ = stack[1].m_obj;
lean_object* v_a_491_ = stack[2].m_obj;
lean_object* v_f_x27_492_ = stack[3].m_obj;
lean_object* v_hf_493_ = stack[4].m_obj;
uint8_t v_done_494_ = stack[5].m_num;
uint8_t v_contextDependent_495_ = stack[6].m_num;
lean_object* v_a_496_ = stack[7].m_obj;
lean_object* v_a_497_ = stack[8].m_obj;
lean_object* v_a_498_ = stack[9].m_obj;
lean_object* v_a_499_ = stack[10].m_obj;
lean_object* v_a_500_ = stack[11].m_obj;
lean_object* v_a_501_ = stack[12].m_obj;
lean_object* v_res_595_;
v_res_595_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_489_, v_f_490_, v_a_491_, v_f_x27_492_, v_hf_493_, v_done_494_, v_contextDependent_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* v_e_596_, lean_object* v_f_597_, lean_object* v_a_598_, lean_object* v_f_x27_599_, lean_object* v_hf_600_, lean_object* v_done_601_, lean_object* v_contextDependent_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
uint8_t v_done_boxed_610_; uint8_t v_contextDependent_boxed_611_; lean_object* v_res_612_; 
v_done_boxed_610_ = lean_unbox(v_done_601_);
v_contextDependent_boxed_611_ = lean_unbox(v_contextDependent_602_);
v_res_612_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_596_, v_f_597_, v_a_598_, v_f_x27_599_, v_hf_600_, v_done_boxed_610_, v_contextDependent_boxed_611_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_612_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* v_e_613_, lean_object* v_f_614_, lean_object* v_a_615_, lean_object* v_f_x27_616_, lean_object* v_hf_617_, lean_object* v_x_618_, uint8_t v_done_619_, uint8_t v_contextDependent_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_613_, v_f_614_, v_a_615_, v_f_x27_616_, v_hf_617_, v_done_619_, v_contextDependent_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
return v___x_628_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_613_ = stack[0].m_obj;
lean_object* v_f_614_ = stack[1].m_obj;
lean_object* v_a_615_ = stack[2].m_obj;
lean_object* v_f_x27_616_ = stack[3].m_obj;
lean_object* v_hf_617_ = stack[4].m_obj;
uint8_t v_done_619_ = stack[6].m_num;
uint8_t v_contextDependent_620_ = stack[7].m_num;
lean_object* v_a_621_ = stack[8].m_obj;
lean_object* v_a_622_ = stack[9].m_obj;
lean_object* v_a_623_ = stack[10].m_obj;
lean_object* v_a_624_ = stack[11].m_obj;
lean_object* v_a_625_ = stack[12].m_obj;
lean_object* v_a_626_ = stack[13].m_obj;
lean_object* v_res_629_;
v_res_629_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(v_e_613_, v_f_614_, v_a_615_, v_f_x27_616_, v_hf_617_, lean_box(0), v_done_619_, v_contextDependent_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* v_e_630_, lean_object* v_f_631_, lean_object* v_a_632_, lean_object* v_f_x27_633_, lean_object* v_hf_634_, lean_object* v_x_635_, lean_object* v_done_636_, lean_object* v_contextDependent_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
uint8_t v_done_boxed_645_; uint8_t v_contextDependent_boxed_646_; lean_object* v_res_647_; 
v_done_boxed_645_ = lean_unbox(v_done_636_);
v_contextDependent_boxed_646_ = lean_unbox(v_contextDependent_637_);
v_res_647_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(v_e_630_, v_f_631_, v_a_632_, v_f_x27_633_, v_hf_634_, v_x_635_, v_done_boxed_645_, v_contextDependent_boxed_646_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
return v_res_647_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* v_00_u03b1_648_, lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_649_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_657_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_649_ = stack[1].m_obj;
lean_object* v___y_650_ = stack[2].m_obj;
lean_object* v___y_651_ = stack[3].m_obj;
lean_object* v___y_652_ = stack[4].m_obj;
lean_object* v___y_653_ = stack[5].m_obj;
lean_object* v___y_654_ = stack[6].m_obj;
lean_object* v___y_655_ = stack[7].m_obj;
lean_object* v_res_658_;
v_res_658_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_box(0), v_msg_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* v_00_u03b1_659_, lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(v_00_u03b1_659_, v_msg_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_668_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_669_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* v_msg_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_6782__overap_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_6782__overap_682_ = lean_panic_fn_borrowed(v___x_681_, v_msg_670_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___y_671_);
v___x_683_ = lean_apply_10(v___x_6782__overap_682_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, lean_box(0));
return v___x_683_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_670_ = stack[0].m_obj;
lean_object* v___y_671_ = stack[1].m_obj;
lean_object* v___y_672_ = stack[2].m_obj;
lean_object* v___y_673_ = stack[3].m_obj;
lean_object* v___y_674_ = stack[4].m_obj;
lean_object* v___y_675_ = stack[5].m_obj;
lean_object* v___y_676_ = stack[6].m_obj;
lean_object* v___y_677_ = stack[7].m_obj;
lean_object* v___y_678_ = stack[8].m_obj;
lean_object* v___y_679_ = stack[9].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
return v_res_696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_701_ = lean_unsigned_to_nat(55u);
v___x_702_ = lean_unsigned_to_nat(139u);
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_705_ = l_mkPanicMessageWithDecl(v___x_704_, v___x_703_, v___x_702_, v___x_701_, v___x_700_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_707_ = lean_unsigned_to_nat(13u);
v___x_708_ = lean_unsigned_to_nat(151u);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_711_ = l_mkPanicMessageWithDecl(v___x_710_, v___x_709_, v___x_708_, v___x_707_, v___x_706_);
return v___x_711_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* v_simpFn_712_, lean_object* v_e_713_, lean_object* v_i_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_nat_dec_eq(v_i_714_, v___x_725_);
if (v___x_726_ == 0)
{
switch(lean_obj_tag(v_e_713_))
{
case 10:
{
lean_object* v_expr_727_; 
v_expr_727_ = lean_ctor_get(v_e_713_, 1);
lean_inc_ref(v_expr_727_);
lean_dec_ref_known(v_e_713_, 2);
v_e_713_ = v_expr_727_;
goto _start;
}
case 5:
{
lean_object* v_fn_729_; lean_object* v_arg_730_; lean_object* v___x_731_; lean_object* v_i_732_; lean_object* v___x_733_; 
v_fn_729_ = lean_ctor_get(v_e_713_, 0);
lean_inc_ref_n(v_fn_729_, 2);
v_arg_730_ = lean_ctor_get(v_e_713_, 1);
lean_inc_ref(v_arg_730_);
v___x_731_ = lean_unsigned_to_nat(1u);
v_i_732_ = lean_nat_sub(v_i_714_, v___x_731_);
v___x_733_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_712_, v_fn_729_, v_i_732_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec(v_i_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
lean_inc_ref(v_fn_729_);
v___x_735_ = l_Lean_Meta_Sym_inferType(v_fn_729_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_Meta_whnfD(v_a_736_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_772_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_772_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_772_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_772_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_a_738_) == 7)
{
lean_object* v_binderType_742_; lean_object* v_body_743_; uint8_t v___x_744_; 
v_binderType_742_ = lean_ctor_get(v_a_738_, 1);
lean_inc_ref(v_binderType_742_);
v_body_743_ = lean_ctor_get(v_a_738_, 2);
lean_inc_ref(v_body_743_);
lean_dec_ref_known(v_a_738_, 3);
v___x_744_ = l_Lean_Expr_hasLooseBVars(v_body_743_);
lean_dec_ref(v_body_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_del_object(v___x_740_);
v___x_745_ = l_Lean_Meta_isProp(v_binderType_742_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; uint8_t v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = lean_unbox(v_a_746_);
lean_dec(v_a_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
lean_inc_ref(v_arg_730_);
v___x_748_ = lean_sym_simp(v_arg_730_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_713_, v_fn_729_, v_arg_730_, v_a_734_, v_a_749_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_750_;
}
else
{
lean_dec(v_a_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref(v_fn_729_);
lean_dec_ref_known(v_e_713_, 2);
return v___x_748_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_751_, 0, v___x_726_);
lean_ctor_set_uint8(v___x_751_, 1, v___x_726_);
v___x_752_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_713_, v_fn_729_, v_arg_730_, v_a_734_, v___x_751_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_752_;
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_a_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref_known(v_e_713_, 2);
lean_dec_ref(v_fn_729_);
v_a_753_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_745_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_745_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_742_);
if (lean_obj_tag(v_a_734_) == 0)
{
uint8_t v_contextDependent_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
lean_dec_ref(v_arg_730_);
lean_dec_ref_known(v_e_713_, 2);
lean_dec_ref(v_fn_729_);
v_contextDependent_761_ = lean_ctor_get_uint8(v_a_734_, 1);
lean_dec_ref_known(v_a_734_, 0);
v___x_762_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_761_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_762_);
v___x_764_ = v___x_740_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v_e_x27_766_; lean_object* v_proof_767_; uint8_t v_contextDependent_768_; lean_object* v___x_769_; 
lean_del_object(v___x_740_);
v_e_x27_766_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref(v_e_x27_766_);
v_proof_767_ = lean_ctor_get(v_a_734_, 1);
lean_inc_ref(v_proof_767_);
v_contextDependent_768_ = lean_ctor_get_uint8(v_a_734_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_734_, 2);
v___x_769_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_713_, v_fn_729_, v_arg_730_, v_e_x27_766_, v_proof_767_, v___x_726_, v_contextDependent_768_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_769_;
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_del_object(v___x_740_);
lean_dec(v_a_738_);
lean_dec(v_a_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref_known(v_e_713_, 2);
lean_dec_ref(v_fn_729_);
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
v___x_771_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_770_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_771_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref_known(v_e_713_, 2);
lean_dec_ref(v_fn_729_);
v_a_773_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_737_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_737_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_a_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref_known(v_e_713_, 2);
lean_dec_ref(v_fn_729_);
v_a_781_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_735_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_735_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_dec_ref(v_arg_730_);
lean_dec_ref_known(v_e_713_, 2);
lean_dec_ref(v_fn_729_);
return v___x_733_;
}
}
default: 
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_e_713_);
lean_dec_ref(v_simpFn_712_);
v___x_789_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
v___x_790_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_789_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_790_;
}
}
}
else
{
lean_object* v___x_791_; 
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_791_ = lean_apply_11(v_simpFn_712_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_791_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpFn_712_ = stack[0].m_obj;
lean_object* v_e_713_ = stack[1].m_obj;
lean_object* v_i_714_ = stack[2].m_obj;
lean_object* v_a_715_ = stack[3].m_obj;
lean_object* v_a_716_ = stack[4].m_obj;
lean_object* v_a_717_ = stack[5].m_obj;
lean_object* v_a_718_ = stack[6].m_obj;
lean_object* v_a_719_ = stack[7].m_obj;
lean_object* v_a_720_ = stack[8].m_obj;
lean_object* v_a_721_ = stack[9].m_obj;
lean_object* v_a_722_ = stack[10].m_obj;
lean_object* v_a_723_ = stack[11].m_obj;
lean_object* v_res_792_;
v_res_792_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_712_, v_e_713_, v_i_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* v_simpFn_793_, lean_object* v_e_794_, lean_object* v_i_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_793_, v_e_794_, v_i_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec(v_i_795_);
return v_res_806_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* v_e_807_, lean_object* v_numArgs_808_, lean_object* v_simpFn_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_809_, v_e_807_, v_numArgs_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
return v___x_820_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpOverApplied_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_807_ = stack[0].m_obj;
lean_object* v_numArgs_808_ = stack[1].m_obj;
lean_object* v_simpFn_809_ = stack[2].m_obj;
lean_object* v_a_810_ = stack[3].m_obj;
lean_object* v_a_811_ = stack[4].m_obj;
lean_object* v_a_812_ = stack[5].m_obj;
lean_object* v_a_813_ = stack[6].m_obj;
lean_object* v_a_814_ = stack[7].m_obj;
lean_object* v_a_815_ = stack[8].m_obj;
lean_object* v_a_816_ = stack[9].m_obj;
lean_object* v_a_817_ = stack[10].m_obj;
lean_object* v_a_818_ = stack[11].m_obj;
lean_object* v_res_821_;
v_res_821_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_807_, v_numArgs_808_, v_simpFn_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* v_e_822_, lean_object* v_numArgs_823_, lean_object* v_simpFn_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_822_, v_numArgs_823_, v_simpFn_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec(v_numArgs_823_);
return v_res_835_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_838_ = lean_unsigned_to_nat(13u);
v___x_839_ = lean_unsigned_to_nat(188u);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_842_ = l_mkPanicMessageWithDecl(v___x_841_, v___x_840_, v___x_839_, v___x_838_, v___x_837_);
return v___x_842_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* v_simpFn_843_, lean_object* v_e_844_, lean_object* v_i_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_nat_dec_eq(v_i_845_, v___x_856_);
if (v___x_857_ == 0)
{
if (lean_obj_tag(v_e_844_) == 5)
{
lean_object* v_fn_858_; lean_object* v_arg_859_; lean_object* v___x_860_; lean_object* v_i_861_; lean_object* v___x_862_; 
v_fn_858_ = lean_ctor_get(v_e_844_, 0);
lean_inc_ref_n(v_fn_858_, 2);
v_arg_859_ = lean_ctor_get(v_e_844_, 1);
lean_inc_ref(v_arg_859_);
v___x_860_ = lean_unsigned_to_nat(1u);
v_i_861_ = lean_nat_sub(v_i_845_, v___x_860_);
v___x_862_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_843_, v_fn_858_, v_i_861_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_i_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
if (lean_obj_tag(v_a_863_) == 0)
{
lean_dec_ref(v_arg_859_);
lean_dec_ref(v_fn_858_);
lean_dec_ref_known(v_e_844_, 2);
return v___x_862_;
}
else
{
lean_object* v_e_x27_864_; lean_object* v_proof_865_; uint8_t v_done_866_; uint8_t v_contextDependent_867_; lean_object* v___x_868_; 
lean_inc_ref(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v_e_x27_864_ = lean_ctor_get(v_a_863_, 0);
lean_inc_ref(v_e_x27_864_);
v_proof_865_ = lean_ctor_get(v_a_863_, 1);
lean_inc_ref(v_proof_865_);
v_done_866_ = lean_ctor_get_uint8(v_a_863_, sizeof(void*)*2);
v_contextDependent_867_ = lean_ctor_get_uint8(v_a_863_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_863_, 2);
v___x_868_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_844_, v_fn_858_, v_arg_859_, v_e_x27_864_, v_proof_865_, v_done_866_, v_contextDependent_867_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v___x_868_;
}
}
else
{
lean_dec_ref(v_arg_859_);
lean_dec_ref(v_fn_858_);
lean_dec_ref_known(v_e_844_, 2);
return v___x_862_;
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v_e_844_);
lean_dec_ref(v_simpFn_843_);
v___x_869_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
v___x_870_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_869_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v___x_870_;
}
}
else
{
lean_object* v___x_871_; 
lean_inc(v_a_854_);
lean_inc_ref(v_a_853_);
lean_inc(v_a_852_);
lean_inc_ref(v_a_851_);
lean_inc(v_a_850_);
lean_inc_ref(v_a_849_);
lean_inc(v_a_848_);
lean_inc_ref(v_a_847_);
lean_inc(v_a_846_);
v___x_871_ = lean_apply_11(v_simpFn_843_, v_e_844_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, lean_box(0));
return v___x_871_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpFn_843_ = stack[0].m_obj;
lean_object* v_e_844_ = stack[1].m_obj;
lean_object* v_i_845_ = stack[2].m_obj;
lean_object* v_a_846_ = stack[3].m_obj;
lean_object* v_a_847_ = stack[4].m_obj;
lean_object* v_a_848_ = stack[5].m_obj;
lean_object* v_a_849_ = stack[6].m_obj;
lean_object* v_a_850_ = stack[7].m_obj;
lean_object* v_a_851_ = stack[8].m_obj;
lean_object* v_a_852_ = stack[9].m_obj;
lean_object* v_a_853_ = stack[10].m_obj;
lean_object* v_a_854_ = stack[11].m_obj;
lean_object* v_res_872_;
v_res_872_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_843_, v_e_844_, v_i_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* v_simpFn_873_, lean_object* v_e_874_, lean_object* v_i_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_873_, v_e_874_, v_i_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_i_875_);
return v_res_886_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* v_e_887_, lean_object* v_numArgs_888_, lean_object* v_simpFn_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(v_simpFn_889_, v_e_887_, v_numArgs_888_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_900_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_propagateOverApplied_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_887_ = stack[0].m_obj;
lean_object* v_numArgs_888_ = stack[1].m_obj;
lean_object* v_simpFn_889_ = stack[2].m_obj;
lean_object* v_a_890_ = stack[3].m_obj;
lean_object* v_a_891_ = stack[4].m_obj;
lean_object* v_a_892_ = stack[5].m_obj;
lean_object* v_a_893_ = stack[6].m_obj;
lean_object* v_a_894_ = stack[7].m_obj;
lean_object* v_a_895_ = stack[8].m_obj;
lean_object* v_a_896_ = stack[9].m_obj;
lean_object* v_a_897_ = stack[10].m_obj;
lean_object* v_a_898_ = stack[11].m_obj;
lean_object* v_res_901_;
v_res_901_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_887_, v_numArgs_888_, v_simpFn_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* v_e_902_, lean_object* v_numArgs_903_, lean_object* v_simpFn_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_902_, v_numArgs_903_, v_simpFn_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec(v_numArgs_903_);
return v_res_915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* v_type_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Expr_isForall(v_type_919_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_whnfD(v_type_919_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Lean_Expr_isForall(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1);
v___x_932_ = l_Lean_MessageData_ofExpr(v_a_929_);
v___x_933_ = l_Lean_indentD(v___x_932_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_934_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Meta_Sym_shareCommonInc(v_a_929_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_944_;
}
}
else
{
return v___x_928_;
}
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_type_919_);
return v___x_945_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_919_ = stack[0].m_obj;
lean_object* v_a_920_ = stack[1].m_obj;
lean_object* v_a_921_ = stack[2].m_obj;
lean_object* v_a_922_ = stack[3].m_obj;
lean_object* v_a_923_ = stack[4].m_obj;
lean_object* v_a_924_ = stack[5].m_obj;
lean_object* v_a_925_ = stack[6].m_obj;
lean_object* v_res_946_;
v_res_946_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* v_type_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_type_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_955_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_956_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_863__overap_966_; lean_object* v___x_967_; 
v___x_965_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
v___x_863__overap_966_ = lean_panic_fn_borrowed(v___x_965_, v_msg_957_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
v___x_967_ = lean_apply_7(v___x_863__overap_966_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, lean_box(0));
return v___x_967_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_957_ = stack[0].m_obj;
lean_object* v___y_958_ = stack[1].m_obj;
lean_object* v___y_959_ = stack[2].m_obj;
lean_object* v___y_960_ = stack[3].m_obj;
lean_object* v___y_961_ = stack[4].m_obj;
lean_object* v___y_962_ = stack[5].m_obj;
lean_object* v___y_963_ = stack[6].m_obj;
lean_object* v_res_968_;
v_res_968_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_980_ = lean_unsigned_to_nat(47u);
v___x_981_ = lean_unsigned_to_nat(219u);
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_984_ = l_mkPanicMessageWithDecl(v___x_983_, v___x_982_, v___x_981_, v___x_980_, v___x_979_);
return v___x_984_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* v_e_985_, lean_object* v_n_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_zero_994_; uint8_t v_isZero_995_; 
v_zero_994_ = lean_unsigned_to_nat(0u);
v_isZero_995_ = lean_nat_dec_eq(v_n_986_, v_zero_994_);
if (v_isZero_995_ == 1)
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Sym_inferType(v_e_985_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_996_;
}
else
{
lean_object* v_one_997_; lean_object* v_n_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_one_997_ = lean_unsigned_to_nat(1u);
v_n_998_ = lean_nat_sub(v_n_986_, v_one_997_);
v___x_999_ = l_Lean_Expr_appFn_x21(v_e_985_);
lean_dec_ref(v_e_985_);
v___x_1000_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v___x_999_, v_n_998_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_n_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_1001_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1013_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
if (lean_obj_tag(v_a_1003_) == 7)
{
lean_object* v_body_1007_; lean_object* v___x_1009_; 
v_body_1007_ = lean_ctor_get(v_a_1003_, 2);
lean_inc_ref(v_body_1007_);
lean_dec_ref_known(v_a_1003_, 3);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_body_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_body_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_del_object(v___x_1005_);
lean_dec(v_a_1003_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
v___x_1012_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_1011_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1012_;
}
}
}
else
{
return v___x_1002_;
}
}
else
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_985_ = stack[0].m_obj;
lean_object* v_n_986_ = stack[1].m_obj;
lean_object* v_a_987_ = stack[2].m_obj;
lean_object* v_a_988_ = stack[3].m_obj;
lean_object* v_a_989_ = stack[4].m_obj;
lean_object* v_a_990_ = stack[5].m_obj;
lean_object* v_a_991_ = stack[6].m_obj;
lean_object* v_a_992_ = stack[7].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_985_, v_n_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* v_e_1015_, lean_object* v_n_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_e_1015_, v_n_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_n_1016_);
return v_res_1024_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* v_f_1025_, lean_object* v_a_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___y_1035_; lean_object* v___x_1038_; uint8_t v_debug_1039_; 
v___x_1038_ = lean_st_ref_get(v___y_1028_);
v_debug_1039_ = lean_ctor_get_uint8(v___x_1038_, sizeof(void*)*12);
lean_dec(v___x_1038_);
if (v_debug_1039_ == 0)
{
v___y_1035_ = v___y_1028_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1025_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1041_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_dec_ref_known(v___x_1041_, 1);
v___y_1035_ = v___y_1028_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_a_1026_);
lean_dec_ref(v_f_1025_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
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
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_a_1026_);
lean_dec_ref(v_f_1025_);
v_a_1050_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1040_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1040_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = l_Lean_Expr_app___override(v_f_1025_, v_a_1026_);
v___x_1037_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1036_, v___y_1035_);
return v___x_1037_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1025_ = stack[0].m_obj;
lean_object* v_a_1026_ = stack[1].m_obj;
lean_object* v___y_1027_ = stack[2].m_obj;
lean_object* v___y_1028_ = stack[3].m_obj;
lean_object* v___y_1029_ = stack[4].m_obj;
lean_object* v___y_1030_ = stack[5].m_obj;
lean_object* v___y_1031_ = stack[6].m_obj;
lean_object* v___y_1032_ = stack[7].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_1025_, v_a_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* v_f_1059_, lean_object* v_a_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_1059_, v_a_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1068_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* v_f_1069_, lean_object* v_a_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_1069_, v_a_1070_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1069_ = stack[0].m_obj;
lean_object* v_a_1070_ = stack[1].m_obj;
lean_object* v___y_1071_ = stack[2].m_obj;
lean_object* v___y_1072_ = stack[3].m_obj;
lean_object* v___y_1073_ = stack[4].m_obj;
lean_object* v___y_1074_ = stack[5].m_obj;
lean_object* v___y_1075_ = stack[6].m_obj;
lean_object* v___y_1076_ = stack[7].m_obj;
lean_object* v___y_1077_ = stack[8].m_obj;
lean_object* v___y_1078_ = stack[9].m_obj;
lean_object* v___y_1079_ = stack[10].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_1069_, v_a_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* v_f_1083_, lean_object* v_a_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_1083_, v_a_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
return v_res_1095_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_27995__overap_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_27995__overap_1108_ = lean_panic_fn_borrowed(v___x_1107_, v_msg_1096_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
v___x_1109_ = lean_apply_10(v___x_27995__overap_1108_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, lean_box(0));
return v___x_1109_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1096_ = stack[0].m_obj;
lean_object* v___y_1097_ = stack[1].m_obj;
lean_object* v___y_1098_ = stack[2].m_obj;
lean_object* v___y_1099_ = stack[3].m_obj;
lean_object* v___y_1100_ = stack[4].m_obj;
lean_object* v___y_1101_ = stack[5].m_obj;
lean_object* v___y_1102_ = stack[6].m_obj;
lean_object* v___y_1103_ = stack[7].m_obj;
lean_object* v___y_1104_ = stack[8].m_obj;
lean_object* v___y_1105_ = stack[9].m_obj;
lean_object* v_res_1110_;
v_res_1110_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
return v_res_1122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
v___x_1128_ = l_Lean_Expr_const___override(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1131_ = lean_unsigned_to_nat(52u);
v___x_1132_ = lean_unsigned_to_nat(281u);
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1135_ = l_mkPanicMessageWithDecl(v___x_1134_, v___x_1133_, v___x_1132_, v___x_1131_, v___x_1130_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1137_ = lean_unsigned_to_nat(52u);
v___x_1138_ = lean_unsigned_to_nat(273u);
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1141_ = l_mkPanicMessageWithDecl(v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_, v___x_1136_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1143_ = lean_unsigned_to_nat(52u);
v___x_1144_ = lean_unsigned_to_nat(288u);
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1147_ = l_mkPanicMessageWithDecl(v___x_1146_, v___x_1145_, v___x_1144_, v___x_1143_, v___x_1142_);
return v___x_1147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1149_ = lean_unsigned_to_nat(26u);
v___x_1150_ = lean_unsigned_to_nat(266u);
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1153_ = l_mkPanicMessageWithDecl(v___x_1152_, v___x_1151_, v___x_1150_, v___x_1149_, v___x_1148_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
v___x_1157_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
return v___x_1158_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* v_i_1159_, lean_object* v_e_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_nat_dec_eq(v_i_1159_, v___x_1171_);
if (v___x_1172_ == 0)
{
if (lean_obj_tag(v_e_1160_) == 5)
{
lean_object* v_fn_1173_; lean_object* v_arg_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_fn_1173_ = lean_ctor_get(v_e_1160_, 0);
lean_inc_ref_n(v_fn_1173_, 2);
v_arg_1174_ = lean_ctor_get(v_e_1160_, 1);
lean_inc_ref(v_arg_1174_);
lean_dec_ref_known(v_e_1160_, 2);
v___x_1175_ = 1;
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_sub(v_i_1159_, v___x_1176_);
v___x_1178_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_1177_, v_fn_1173_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1436_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v_fst_1180_ = lean_ctor_get(v_a_1179_, 0);
v_snd_1181_ = lean_ctor_get(v_a_1179_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_a_1179_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1183_ = v_a_1179_;
v_isShared_1184_ = v_isSharedCheck_1436_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snd_1181_);
lean_inc(v_fst_1180_);
lean_dec(v_a_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1436_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; 
lean_inc(v_a_1169_);
lean_inc_ref(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc(v_a_1165_);
lean_inc_ref(v_a_1164_);
lean_inc(v_a_1163_);
lean_inc_ref(v_a_1162_);
lean_inc(v_a_1161_);
lean_inc_ref(v_arg_1174_);
v___x_1185_ = lean_sym_simp(v_arg_1174_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1427_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1427_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1427_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___y_1191_; 
if (lean_obj_tag(v_fst_1180_) == 0)
{
lean_dec(v_snd_1181_);
if (lean_obj_tag(v_a_1186_) == 0)
{
uint8_t v_contextDependent_1200_; 
lean_dec(v___x_1177_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_contextDependent_1200_ = lean_ctor_get_uint8(v_fst_1180_, 1);
lean_dec_ref_known(v_fst_1180_, 0);
if (v_contextDependent_1200_ == 0)
{
uint8_t v_contextDependent_1201_; 
v_contextDependent_1201_ = lean_ctor_get_uint8(v_a_1186_, 1);
lean_dec_ref_known(v_a_1186_, 0);
v___y_1191_ = v_contextDependent_1201_;
goto v___jp_1190_;
}
else
{
lean_dec_ref_known(v_a_1186_, 0);
v___y_1191_ = v___x_1175_;
goto v___jp_1190_;
}
}
else
{
uint8_t v_contextDependent_1202_; lean_object* v_e_x27_1203_; lean_object* v_proof_1204_; uint8_t v_contextDependent_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1282_; 
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
v_contextDependent_1202_ = lean_ctor_get_uint8(v_fst_1180_, 1);
lean_dec_ref_known(v_fst_1180_, 0);
v_e_x27_1203_ = lean_ctor_get(v_a_1186_, 0);
v_proof_1204_ = lean_ctor_get(v_a_1186_, 1);
v_contextDependent_1205_ = lean_ctor_get_uint8(v_a_1186_, sizeof(void*)*2 + 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_a_1186_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1207_ = v_a_1186_;
v_isShared_1208_ = v_isSharedCheck_1282_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_proof_1204_);
lean_inc(v_e_x27_1203_);
lean_dec(v_a_1186_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1282_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; 
lean_inc_ref(v_fn_1173_);
v___x_1209_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(v_fn_1173_, v___x_1177_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v___x_1177_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1211_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_a_1210_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
if (lean_obj_tag(v_a_1212_) == 7)
{
lean_object* v_binderType_1213_; lean_object* v_body_1214_; lean_object* v___x_1215_; 
v_binderType_1213_ = lean_ctor_get(v_a_1212_, 1);
lean_inc_ref(v_binderType_1213_);
v_body_1214_ = lean_ctor_get(v_a_1212_, 2);
lean_inc_ref(v_body_1214_);
lean_dec_ref_known(v_a_1212_, 3);
lean_inc_ref(v_e_x27_1203_);
lean_inc_ref(v_fn_1173_);
v___x_1215_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_1173_, v_e_x27_1203_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
lean_inc_ref(v_binderType_1213_);
v___x_1217_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1213_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
lean_inc_ref(v_body_1214_);
v___x_1219_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1214_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1239_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1239_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1239_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___y_1231_; 
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1));
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1220_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1218_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_mkConst(v___x_1224_, v___x_1227_);
lean_inc_ref(v_body_1214_);
v___x_1229_ = l_Lean_mkApp6(v___x_1228_, v_binderType_1213_, v_body_1214_, v_arg_1174_, v_e_x27_1203_, v_fn_1173_, v_proof_1204_);
if (v_contextDependent_1202_ == 0)
{
v___y_1231_ = v_contextDependent_1205_;
goto v___jp_1230_;
}
else
{
v___y_1231_ = v___x_1175_;
goto v___jp_1230_;
}
v___jp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1229_);
lean_ctor_set(v___x_1207_, 0, v_a_1216_);
v___x_1233_ = v___x_1207_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1216_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___x_1229_);
v___x_1233_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*2, v___x_1172_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*2 + 1, v___y_1231_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_body_1214_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1234_);
v___x_1236_ = v___x_1222_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1218_);
lean_dec(v_a_1216_);
lean_dec_ref(v_body_1214_);
lean_dec_ref(v_binderType_1213_);
lean_del_object(v___x_1207_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1240_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1219_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1219_);
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
lean_dec(v_a_1216_);
lean_dec_ref(v_body_1214_);
lean_dec_ref(v_binderType_1213_);
lean_del_object(v___x_1207_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1248_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1217_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1217_);
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
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_body_1214_);
lean_dec_ref(v_binderType_1213_);
lean_del_object(v___x_1207_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1256_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1215_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1215_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_a_1212_);
lean_del_object(v___x_1207_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
v___x_1265_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1264_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1265_;
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_del_object(v___x_1207_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1266_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1211_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1211_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_del_object(v___x_1207_);
lean_dec_ref(v_proof_1204_);
lean_dec_ref(v_e_x27_1203_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1274_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1209_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1209_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
lean_dec(v___x_1177_);
if (lean_obj_tag(v_a_1186_) == 0)
{
lean_object* v_e_x27_1283_; lean_object* v_proof_1284_; uint8_t v_contextDependent_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1353_; 
v_e_x27_1283_ = lean_ctor_get(v_fst_1180_, 0);
v_proof_1284_ = lean_ctor_get(v_fst_1180_, 1);
v_contextDependent_1285_ = lean_ctor_get_uint8(v_fst_1180_, sizeof(void*)*2 + 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_fst_1180_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1287_ = v_fst_1180_;
v_isShared_1288_ = v_isSharedCheck_1353_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_proof_1284_);
lean_inc(v_e_x27_1283_);
lean_dec(v_fst_1180_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1353_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
uint8_t v_contextDependent_1289_; lean_object* v___x_1290_; 
v_contextDependent_1289_ = lean_ctor_get_uint8(v_a_1186_, 1);
lean_dec_ref_known(v_a_1186_, 0);
v___x_1290_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1181_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
if (lean_obj_tag(v_a_1291_) == 7)
{
lean_object* v_binderType_1292_; lean_object* v_body_1293_; lean_object* v___x_1294_; 
v_binderType_1292_ = lean_ctor_get(v_a_1291_, 1);
lean_inc_ref(v_binderType_1292_);
v_body_1293_ = lean_ctor_get(v_a_1291_, 2);
lean_inc_ref(v_body_1293_);
lean_dec_ref_known(v_a_1291_, 3);
lean_inc_ref(v_arg_1174_);
lean_inc_ref(v_e_x27_1283_);
v___x_1294_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1283_, v_arg_1174_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
lean_inc_ref(v_binderType_1292_);
v___x_1296_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1292_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
lean_inc_ref(v_body_1293_);
v___x_1298_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1293_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1318_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1318_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1318_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___y_1310_; 
v___x_1303_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3));
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1305_, 0, v_a_1299_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_a_1297_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Lean_mkConst(v___x_1303_, v___x_1306_);
lean_inc_ref(v_body_1293_);
v___x_1308_ = l_Lean_mkApp6(v___x_1307_, v_binderType_1292_, v_body_1293_, v_fn_1173_, v_e_x27_1283_, v_proof_1284_, v_arg_1174_);
if (v_contextDependent_1285_ == 0)
{
v___y_1310_ = v_contextDependent_1289_;
goto v___jp_1309_;
}
else
{
v___y_1310_ = v___x_1175_;
goto v___jp_1309_;
}
v___jp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1308_);
lean_ctor_set(v___x_1287_, 0, v_a_1295_);
v___x_1312_ = v___x_1287_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1295_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1308_);
v___x_1312_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*2, v___x_1172_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*2 + 1, v___y_1310_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_body_1293_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1313_);
v___x_1315_ = v___x_1301_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1297_);
lean_dec(v_a_1295_);
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_del_object(v___x_1287_);
lean_dec_ref(v_proof_1284_);
lean_dec_ref(v_e_x27_1283_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1319_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1298_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1298_);
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
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_a_1295_);
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_del_object(v___x_1287_);
lean_dec_ref(v_proof_1284_);
lean_dec_ref(v_e_x27_1283_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1327_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1296_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1296_);
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
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_del_object(v___x_1287_);
lean_dec_ref(v_proof_1284_);
lean_dec_ref(v_e_x27_1283_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1335_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1294_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1294_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_a_1291_);
lean_del_object(v___x_1287_);
lean_dec_ref(v_proof_1284_);
lean_dec_ref(v_e_x27_1283_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v___x_1343_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
v___x_1344_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1343_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1344_;
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_del_object(v___x_1287_);
lean_dec_ref(v_proof_1284_);
lean_dec_ref(v_e_x27_1283_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1345_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1290_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1290_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1354_; lean_object* v_proof_1355_; uint8_t v_contextDependent_1356_; lean_object* v_e_x27_1357_; lean_object* v_proof_1358_; uint8_t v_contextDependent_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1426_; 
v_e_x27_1354_ = lean_ctor_get(v_fst_1180_, 0);
lean_inc_ref(v_e_x27_1354_);
v_proof_1355_ = lean_ctor_get(v_fst_1180_, 1);
lean_inc_ref(v_proof_1355_);
v_contextDependent_1356_ = lean_ctor_get_uint8(v_fst_1180_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1180_, 2);
v_e_x27_1357_ = lean_ctor_get(v_a_1186_, 0);
v_proof_1358_ = lean_ctor_get(v_a_1186_, 1);
v_contextDependent_1359_ = lean_ctor_get_uint8(v_a_1186_, sizeof(void*)*2 + 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_a_1186_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1361_ = v_a_1186_;
v_isShared_1362_ = v_isSharedCheck_1426_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_proof_1358_);
lean_inc(v_e_x27_1357_);
lean_dec(v_a_1186_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1426_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; 
v___x_1363_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(v_snd_1181_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
if (lean_obj_tag(v_a_1364_) == 7)
{
lean_object* v_binderType_1365_; lean_object* v_body_1366_; lean_object* v___x_1367_; 
v_binderType_1365_ = lean_ctor_get(v_a_1364_, 1);
lean_inc_ref(v_binderType_1365_);
v_body_1366_ = lean_ctor_get(v_a_1364_, 2);
lean_inc_ref(v_body_1366_);
lean_dec_ref_known(v_a_1364_, 3);
lean_inc_ref(v_e_x27_1357_);
lean_inc_ref(v_e_x27_1354_);
v___x_1367_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_1354_, v_e_x27_1357_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
lean_inc_ref(v_binderType_1365_);
v___x_1369_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1365_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
lean_inc_ref(v_body_1366_);
v___x_1371_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1366_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1391_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1391_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1391_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___y_1383_; 
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5));
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_a_1372_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_a_1370_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_mkConst(v___x_1376_, v___x_1379_);
lean_inc_ref(v_body_1366_);
v___x_1381_ = l_Lean_mkApp8(v___x_1380_, v_binderType_1365_, v_body_1366_, v_fn_1173_, v_e_x27_1354_, v_arg_1174_, v_e_x27_1357_, v_proof_1355_, v_proof_1358_);
if (v_contextDependent_1356_ == 0)
{
v___y_1383_ = v_contextDependent_1359_;
goto v___jp_1382_;
}
else
{
v___y_1383_ = v___x_1175_;
goto v___jp_1382_;
}
v___jp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1381_);
lean_ctor_set(v___x_1361_, 0, v_a_1368_);
v___x_1385_ = v___x_1361_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1368_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1381_);
v___x_1385_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*2, v___x_1172_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*2 + 1, v___y_1383_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_body_1366_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1386_);
v___x_1388_ = v___x_1374_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_a_1370_);
lean_dec(v_a_1368_);
lean_dec_ref(v_body_1366_);
lean_dec_ref(v_binderType_1365_);
lean_del_object(v___x_1361_);
lean_dec_ref(v_proof_1358_);
lean_dec_ref(v_e_x27_1357_);
lean_dec_ref(v_proof_1355_);
lean_dec_ref(v_e_x27_1354_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1392_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1371_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1371_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1368_);
lean_dec_ref(v_body_1366_);
lean_dec_ref(v_binderType_1365_);
lean_del_object(v___x_1361_);
lean_dec_ref(v_proof_1358_);
lean_dec_ref(v_e_x27_1357_);
lean_dec_ref(v_proof_1355_);
lean_dec_ref(v_e_x27_1354_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1400_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1369_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1369_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_body_1366_);
lean_dec_ref(v_binderType_1365_);
lean_del_object(v___x_1361_);
lean_dec_ref(v_proof_1358_);
lean_dec_ref(v_e_x27_1357_);
lean_dec_ref(v_proof_1355_);
lean_dec_ref(v_e_x27_1354_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1408_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1367_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1367_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v_a_1364_);
lean_del_object(v___x_1361_);
lean_dec_ref(v_proof_1358_);
lean_dec_ref(v_e_x27_1357_);
lean_dec_ref(v_proof_1355_);
lean_dec_ref(v_e_x27_1354_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v___x_1416_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
v___x_1417_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1416_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1417_;
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_del_object(v___x_1361_);
lean_dec_ref(v_proof_1358_);
lean_dec_ref(v_e_x27_1357_);
lean_dec_ref(v_proof_1355_);
lean_dec_ref(v_e_x27_1354_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1418_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1363_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1363_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1191_);
v___x_1193_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v___x_1193_);
lean_ctor_set(v___x_1183_, 0, v___x_1192_);
v___x_1195_ = v___x_1183_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1195_);
v___x_1197_ = v___x_1188_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
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
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_del_object(v___x_1183_);
lean_dec(v_snd_1181_);
lean_dec(v_fst_1180_);
lean_dec(v___x_1177_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
v_a_1428_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1185_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1185_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_dec(v___x_1177_);
lean_dec_ref(v_arg_1174_);
lean_dec_ref(v_fn_1173_);
return v___x_1178_;
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_e_1160_);
v___x_1437_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
v___x_1438_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_1437_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_e_1160_);
v___x_1439_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1159_ = stack[0].m_obj;
lean_object* v_e_1160_ = stack[1].m_obj;
lean_object* v_a_1161_ = stack[2].m_obj;
lean_object* v_a_1162_ = stack[3].m_obj;
lean_object* v_a_1163_ = stack[4].m_obj;
lean_object* v_a_1164_ = stack[5].m_obj;
lean_object* v_a_1165_ = stack[6].m_obj;
lean_object* v_a_1166_ = stack[7].m_obj;
lean_object* v_a_1167_ = stack[8].m_obj;
lean_object* v_a_1168_ = stack[9].m_obj;
lean_object* v_a_1169_ = stack[10].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1159_, v_e_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* v_i_1442_, lean_object* v_e_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_i_1442_, v_e_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec(v_i_1442_);
return v_res_1454_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* v_n_1455_, lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v_n_1455_, v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_fst_1472_; lean_object* v___x_1474_; 
v_fst_1472_ = lean_ctor_get(v_a_1468_, 0);
lean_inc(v_fst_1472_);
lean_dec(v_a_1468_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_fst_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_fst_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_a_1477_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1467_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1467_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1455_ = stack[0].m_obj;
lean_object* v_e_1456_ = stack[1].m_obj;
lean_object* v_a_1457_ = stack[2].m_obj;
lean_object* v_a_1458_ = stack[3].m_obj;
lean_object* v_a_1459_ = stack[4].m_obj;
lean_object* v_a_1460_ = stack[5].m_obj;
lean_object* v_a_1461_ = stack[6].m_obj;
lean_object* v_a_1462_ = stack[7].m_obj;
lean_object* v_a_1463_ = stack[8].m_obj;
lean_object* v_a_1464_ = stack[9].m_obj;
lean_object* v_a_1465_ = stack[10].m_obj;
lean_object* v_res_1485_;
v_res_1485_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1455_, v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
stack->m_obj
 = v_res_1485_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* v_n_1486_, lean_object* v_e_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v_n_1486_, v_e_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_n_1486_);
return v_res_1498_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* v_e_1499_, lean_object* v_prefixSize_1500_, lean_object* v_suffixSize_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_numArgs_1512_; uint8_t v___x_1513_; 
v_numArgs_1512_ = l_Lean_Expr_getAppNumArgs(v_e_1499_);
v___x_1513_ = lean_nat_dec_le(v_numArgs_1512_, v_prefixSize_1500_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_nat_add(v_prefixSize_1500_, v_suffixSize_1501_);
v___x_1515_ = lean_nat_dec_lt(v___x_1514_, v_numArgs_1512_);
lean_dec(v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_suffixSize_1501_);
v___x_1516_ = lean_nat_sub(v_numArgs_1512_, v_prefixSize_1500_);
lean_dec(v_numArgs_1512_);
v___x_1517_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(v___x_1516_, v_e_1499_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v___x_1516_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_nat_sub(v_numArgs_1512_, v_prefixSize_1500_);
lean_dec(v_numArgs_1512_);
v___x_1519_ = lean_nat_sub(v___x_1518_, v_suffixSize_1501_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(v___x_1520_, 0, v_suffixSize_1501_);
v___x_1521_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___x_1520_, v_e_1499_, v___x_1519_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v___x_1519_);
return v___x_1521_;
}
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_dec(v_numArgs_1512_);
lean_dec(v_suffixSize_1501_);
lean_dec_ref(v_e_1499_);
v___x_1522_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpFixedPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1499_ = stack[0].m_obj;
lean_object* v_prefixSize_1500_ = stack[1].m_obj;
lean_object* v_suffixSize_1501_ = stack[2].m_obj;
lean_object* v_a_1502_ = stack[3].m_obj;
lean_object* v_a_1503_ = stack[4].m_obj;
lean_object* v_a_1504_ = stack[5].m_obj;
lean_object* v_a_1505_ = stack[6].m_obj;
lean_object* v_a_1506_ = stack[7].m_obj;
lean_object* v_a_1507_ = stack[8].m_obj;
lean_object* v_a_1508_ = stack[9].m_obj;
lean_object* v_a_1509_ = stack[10].m_obj;
lean_object* v_a_1510_ = stack[11].m_obj;
lean_object* v_res_1524_;
v_res_1524_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1499_, v_prefixSize_1500_, v_suffixSize_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
stack->m_obj
 = v_res_1524_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* v_e_1525_, lean_object* v_prefixSize_1526_, lean_object* v_suffixSize_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_1525_, v_prefixSize_1526_, v_suffixSize_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec(v_prefixSize_1526_);
return v_res_1538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1541_ = lean_unsigned_to_nat(13u);
v___x_1542_ = lean_unsigned_to_nat(324u);
v___x_1543_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
v___x_1544_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1545_ = l_mkPanicMessageWithDecl(v___x_1544_, v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_);
return v___x_1545_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* v_rewritable_1546_, lean_object* v_i_1547_, lean_object* v_e_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = lean_nat_dec_eq(v_i_1547_, v___x_1559_);
if (v___x_1560_ == 0)
{
if (lean_obj_tag(v_e_1548_) == 5)
{
lean_object* v_fn_1561_; lean_object* v_arg_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_fn_1561_ = lean_ctor_get(v_e_1548_, 0);
lean_inc_ref_n(v_fn_1561_, 2);
v_arg_1562_ = lean_ctor_get(v_e_1548_, 1);
lean_inc_ref(v_arg_1562_);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_sub(v_i_1547_, v___x_1563_);
v___x_1565_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1546_, v___x_1564_, v_fn_1561_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1585_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1585_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1585_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_array_fget_borrowed(v_rewritable_1546_, v___x_1564_);
lean_dec(v___x_1564_);
v___x_1571_ = lean_unbox(v___x_1570_);
if (v___x_1571_ == 0)
{
if (lean_obj_tag(v_a_1566_) == 0)
{
uint8_t v_contextDependent_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec_ref(v_arg_1562_);
lean_dec_ref_known(v_e_1548_, 2);
lean_dec_ref(v_fn_1561_);
v_contextDependent_1572_ = lean_ctor_get_uint8(v_a_1566_, 1);
lean_dec_ref_known(v_a_1566_, 0);
v___x_1573_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1572_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1573_);
v___x_1575_ = v___x_1568_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v_e_x27_1577_; lean_object* v_proof_1578_; uint8_t v_contextDependent_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; 
lean_del_object(v___x_1568_);
v_e_x27_1577_ = lean_ctor_get(v_a_1566_, 0);
lean_inc_ref(v_e_x27_1577_);
v_proof_1578_ = lean_ctor_get(v_a_1566_, 1);
lean_inc_ref(v_proof_1578_);
v_contextDependent_1579_ = lean_ctor_get_uint8(v_a_1566_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1566_, 2);
v___x_1580_ = lean_unbox(v___x_1570_);
v___x_1581_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_1548_, v_fn_1561_, v_arg_1562_, v_e_x27_1577_, v_proof_1578_, v___x_1580_, v_contextDependent_1579_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
return v___x_1581_;
}
}
else
{
lean_object* v___x_1582_; 
lean_del_object(v___x_1568_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
lean_inc(v_a_1551_);
lean_inc_ref(v_a_1550_);
lean_inc(v_a_1549_);
lean_inc_ref(v_arg_1562_);
v___x_1582_ = lean_sym_simp(v_arg_1562_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_1548_, v_fn_1561_, v_arg_1562_, v_a_1566_, v_a_1583_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
return v___x_1584_;
}
else
{
lean_dec(v_a_1566_);
lean_dec_ref(v_arg_1562_);
lean_dec_ref_known(v_e_1548_, 2);
lean_dec_ref(v_fn_1561_);
return v___x_1582_;
}
}
}
}
else
{
lean_dec(v___x_1564_);
lean_dec_ref(v_arg_1562_);
lean_dec_ref_known(v_e_1548_, 2);
lean_dec_ref(v_fn_1561_);
return v___x_1565_;
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec_ref(v_e_1548_);
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
v___x_1587_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1586_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
return v___x_1587_;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_e_1548_);
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_rewritable_1546_ = stack[0].m_obj;
lean_object* v_i_1547_ = stack[1].m_obj;
lean_object* v_e_1548_ = stack[2].m_obj;
lean_object* v_a_1549_ = stack[3].m_obj;
lean_object* v_a_1550_ = stack[4].m_obj;
lean_object* v_a_1551_ = stack[5].m_obj;
lean_object* v_a_1552_ = stack[6].m_obj;
lean_object* v_a_1553_ = stack[7].m_obj;
lean_object* v_a_1554_ = stack[8].m_obj;
lean_object* v_a_1555_ = stack[9].m_obj;
lean_object* v_a_1556_ = stack[10].m_obj;
lean_object* v_a_1557_ = stack[11].m_obj;
lean_object* v_res_1590_;
v_res_1590_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1546_, v_i_1547_, v_e_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
stack->m_obj
 = v_res_1590_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* v_rewritable_1591_, lean_object* v_i_1592_, lean_object* v_e_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1591_, v_i_1592_, v_e_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec(v_i_1592_);
lean_dec_ref(v_rewritable_1591_);
return v_res_1604_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* v_rewritable_1605_, lean_object* v_i_1606_, lean_object* v_e_1607_, lean_object* v_h_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1605_, v_i_1606_, v_e_1607_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_rewritable_1605_ = stack[0].m_obj;
lean_object* v_i_1606_ = stack[1].m_obj;
lean_object* v_e_1607_ = stack[2].m_obj;
lean_object* v_a_1609_ = stack[4].m_obj;
lean_object* v_a_1610_ = stack[5].m_obj;
lean_object* v_a_1611_ = stack[6].m_obj;
lean_object* v_a_1612_ = stack[7].m_obj;
lean_object* v_a_1613_ = stack[8].m_obj;
lean_object* v_a_1614_ = stack[9].m_obj;
lean_object* v_a_1615_ = stack[10].m_obj;
lean_object* v_a_1616_ = stack[11].m_obj;
lean_object* v_a_1617_ = stack[12].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1605_, v_i_1606_, v_e_1607_, lean_box(0), v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
stack->m_obj
 = v_res_1620_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* v_rewritable_1621_, lean_object* v_i_1622_, lean_object* v_e_1623_, lean_object* v_h_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(v_rewritable_1621_, v_i_1622_, v_e_1623_, v_h_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec(v_i_1622_);
lean_dec_ref(v_rewritable_1621_);
return v_res_1635_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* v_rewritable_1636_, lean_object* v___x_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1636_, v___x_1637_, v_x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_rewritable_1636_ = stack[0].m_obj;
lean_object* v___x_1637_ = stack[1].m_obj;
lean_object* v_x_1638_ = stack[2].m_obj;
lean_object* v___y_1639_ = stack[3].m_obj;
lean_object* v___y_1640_ = stack[4].m_obj;
lean_object* v___y_1641_ = stack[5].m_obj;
lean_object* v___y_1642_ = stack[6].m_obj;
lean_object* v___y_1643_ = stack[7].m_obj;
lean_object* v___y_1644_ = stack[8].m_obj;
lean_object* v___y_1645_ = stack[9].m_obj;
lean_object* v___y_1646_ = stack[10].m_obj;
lean_object* v___y_1647_ = stack[11].m_obj;
lean_object* v_res_1650_;
v_res_1650_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1636_, v___x_1637_, v_x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
stack->m_obj
 = v_res_1650_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* v_rewritable_1651_, lean_object* v___x_1652_, lean_object* v_x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(v_rewritable_1651_, v___x_1652_, v_x_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec(v___x_1652_);
lean_dec_ref(v_rewritable_1651_);
return v_res_1664_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* v_e_1665_, lean_object* v_rewritable_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_numArgs_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_numArgs_1677_ = l_Lean_Expr_getAppNumArgs(v_e_1665_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_nat_dec_eq(v_numArgs_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = lean_array_get_size(v_rewritable_1666_);
v___x_1681_ = lean_nat_dec_lt(v___x_1680_, v_numArgs_1677_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_1666_, v_numArgs_1677_, v_e_1665_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_numArgs_1677_);
lean_dec_ref(v_rewritable_1666_);
return v___x_1682_;
}
else
{
lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___f_1683_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1683_, 0, v_rewritable_1666_);
lean_closure_set(v___f_1683_, 1, v___x_1680_);
v___x_1684_ = lean_nat_sub(v_numArgs_1677_, v___x_1680_);
lean_dec(v_numArgs_1677_);
v___x_1685_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_1683_, v_e_1665_, v___x_1684_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v___x_1684_);
return v___x_1685_;
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_numArgs_1677_);
lean_dec_ref(v_rewritable_1666_);
lean_dec_ref(v_e_1665_);
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpInterlaced_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1665_ = stack[0].m_obj;
lean_object* v_rewritable_1666_ = stack[1].m_obj;
lean_object* v_a_1667_ = stack[2].m_obj;
lean_object* v_a_1668_ = stack[3].m_obj;
lean_object* v_a_1669_ = stack[4].m_obj;
lean_object* v_a_1670_ = stack[5].m_obj;
lean_object* v_a_1671_ = stack[6].m_obj;
lean_object* v_a_1672_ = stack[7].m_obj;
lean_object* v_a_1673_ = stack[8].m_obj;
lean_object* v_a_1674_ = stack[9].m_obj;
lean_object* v_a_1675_ = stack[10].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1665_, v_rewritable_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
stack->m_obj
 = v_res_1688_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* v_e_1689_, lean_object* v_rewritable_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_1689_, v_rewritable_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* v_argResults_1702_, lean_object* v_numEqs_1703_, lean_object* v_result_1704_){
_start:
{
if (lean_obj_tag(v_result_1704_) == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
lean_dec(v_numEqs_1703_);
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = lean_array_get_size(v_argResults_1702_);
v___x_1707_ = lean_nat_dec_lt(v___x_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_dec_ref_known(v_result_1704_, 0);
return v_argResults_1702_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_array_push(v_argResults_1702_, v_result_1704_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = lean_array_get_size(v_argResults_1702_);
v___x_1710_ = lean_nat_dec_lt(v___x_1709_, v_numEqs_1703_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_numEqs_1703_);
v___x_1711_ = lean_array_push(v_argResults_1702_, v_result_1704_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v_argResults_1702_);
v___x_1712_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_1713_ = lean_mk_array(v_numEqs_1703_, v___x_1712_);
v___x_1714_ = lean_array_push(v___x_1713_, v_result_1704_);
return v___x_1714_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1717_ = lean_unsigned_to_nat(13u);
v___x_1718_ = lean_unsigned_to_nat(445u);
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1721_ = l_mkPanicMessageWithDecl(v___x_1720_, v___x_1719_, v___x_1718_, v___x_1717_, v___x_1716_);
return v___x_1721_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* v_argKinds_1722_, lean_object* v_mkNonRflResult_1723_, lean_object* v_e_1724_, lean_object* v_i_1725_, lean_object* v_numEqs_1726_, lean_object* v_argResults_1727_, uint8_t v_anyCD_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
if (lean_obj_tag(v_e_1724_) == 5)
{
lean_object* v_fn_1739_; lean_object* v_arg_1740_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_fn_1739_ = lean_ctor_get(v_e_1724_, 0);
lean_inc_ref(v_fn_1739_);
v_arg_1740_ = lean_ctor_get(v_e_1724_, 1);
lean_inc_ref(v_arg_1740_);
lean_dec_ref_known(v_e_1724_, 2);
v___x_1754_ = 0;
v___x_1755_ = lean_box(v___x_1754_);
v___x_1756_ = lean_array_get(v___x_1755_, v_argKinds_1722_, v_i_1725_);
lean_dec(v___x_1755_);
v___x_1757_ = lean_unbox(v___x_1756_);
lean_dec(v___x_1756_);
switch(v___x_1757_)
{
case 5:
{
lean_dec_ref(v_arg_1740_);
v___y_1742_ = v_a_1729_;
v___y_1743_ = v_a_1730_;
v___y_1744_ = v_a_1731_;
v___y_1745_ = v_a_1732_;
v___y_1746_ = v_a_1733_;
v___y_1747_ = v_a_1734_;
v___y_1748_ = v_a_1735_;
v___y_1749_ = v_a_1736_;
v___y_1750_ = v_a_1737_;
goto v___jp_1741_;
}
case 0:
{
lean_dec_ref(v_arg_1740_);
v___y_1742_ = v_a_1729_;
v___y_1743_ = v_a_1730_;
v___y_1744_ = v_a_1731_;
v___y_1745_ = v_a_1732_;
v___y_1746_ = v_a_1733_;
v___y_1747_ = v_a_1734_;
v___y_1748_ = v_a_1735_;
v___y_1749_ = v_a_1736_;
v___y_1750_ = v_a_1737_;
goto v___jp_1741_;
}
case 3:
{
lean_dec_ref(v_arg_1740_);
v___y_1742_ = v_a_1729_;
v___y_1743_ = v_a_1730_;
v___y_1744_ = v_a_1731_;
v___y_1745_ = v_a_1732_;
v___y_1746_ = v_a_1733_;
v___y_1747_ = v_a_1734_;
v___y_1748_ = v_a_1735_;
v___y_1749_ = v_a_1736_;
v___y_1750_ = v_a_1737_;
goto v___jp_1741_;
}
case 2:
{
lean_object* v___x_1758_; 
lean_inc(v_a_1737_);
lean_inc_ref(v_a_1736_);
lean_inc(v_a_1735_);
lean_inc_ref(v_a_1734_);
lean_inc(v_a_1733_);
lean_inc_ref(v_a_1732_);
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
v___x_1758_ = lean_sym_simp(v_arg_1740_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_n(v_a_1759_, 2);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_sub(v_i_1725_, v___x_1760_);
lean_dec(v_i_1725_);
v___x_1762_ = lean_nat_add(v_numEqs_1726_, v___x_1760_);
v___x_1763_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_1727_, v_numEqs_1726_, v_a_1759_);
if (v_anyCD_1728_ == 0)
{
if (lean_obj_tag(v_a_1759_) == 0)
{
uint8_t v_contextDependent_1764_; 
v_contextDependent_1764_ = lean_ctor_get_uint8(v_a_1759_, 1);
lean_dec_ref_known(v_a_1759_, 0);
v_e_1724_ = v_fn_1739_;
v_i_1725_ = v___x_1761_;
v_numEqs_1726_ = v___x_1762_;
v_argResults_1727_ = v___x_1763_;
v_anyCD_1728_ = v_contextDependent_1764_;
goto _start;
}
else
{
uint8_t v_contextDependent_1766_; 
v_contextDependent_1766_ = lean_ctor_get_uint8(v_a_1759_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1759_, 2);
v_e_1724_ = v_fn_1739_;
v_i_1725_ = v___x_1761_;
v_numEqs_1726_ = v___x_1762_;
v_argResults_1727_ = v___x_1763_;
v_anyCD_1728_ = v_contextDependent_1766_;
goto _start;
}
}
else
{
lean_dec(v_a_1759_);
v_e_1724_ = v_fn_1739_;
v_i_1725_ = v___x_1761_;
v_numEqs_1726_ = v___x_1762_;
v_argResults_1727_ = v___x_1763_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_1739_);
lean_dec_ref(v_argResults_1727_);
lean_dec(v_numEqs_1726_);
lean_dec(v_i_1725_);
lean_dec_ref(v_mkNonRflResult_1723_);
return v___x_1758_;
}
}
default: 
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_fn_1739_);
lean_dec_ref(v_argResults_1727_);
lean_dec(v_numEqs_1726_);
lean_dec(v_i_1725_);
lean_dec_ref(v_mkNonRflResult_1723_);
v___x_1769_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
v___x_1770_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_1769_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
return v___x_1770_;
}
}
v___jp_1741_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_nat_sub(v_i_1725_, v___x_1751_);
lean_dec(v_i_1725_);
v_e_1724_ = v_fn_1739_;
v_i_1725_ = v___x_1752_;
v_a_1729_ = v___y_1742_;
v_a_1730_ = v___y_1743_;
v_a_1731_ = v___y_1744_;
v_a_1732_ = v___y_1745_;
v_a_1733_ = v___y_1746_;
v_a_1734_ = v___y_1747_;
v_a_1735_ = v___y_1748_;
v_a_1736_ = v___y_1749_;
v_a_1737_ = v___y_1750_;
goto _start;
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
lean_dec(v_numEqs_1726_);
lean_dec(v_i_1725_);
lean_dec_ref(v_e_1724_);
v___x_1771_ = lean_array_get_size(v_argResults_1727_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_nat_dec_eq(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = l_Array_reverse___redArg(v_argResults_1727_);
lean_inc(v_a_1737_);
lean_inc_ref(v_a_1736_);
lean_inc(v_a_1735_);
lean_inc_ref(v_a_1734_);
lean_inc(v_a_1733_);
lean_inc_ref(v_a_1732_);
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
v___x_1775_ = lean_apply_11(v_mkNonRflResult_1723_, v___x_1774_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
if (v_anyCD_1728_ == 0)
{
lean_dec(v_a_1776_);
return v___x_1775_;
}
else
{
if (lean_obj_tag(v_a_1776_) == 0)
{
uint8_t v_contextDependent_1780_; 
v_contextDependent_1780_ = lean_ctor_get_uint8(v_a_1776_, 1);
if (v_contextDependent_1780_ == 0)
{
lean_dec_ref_known(v___x_1775_, 1);
goto v___jp_1777_;
}
else
{
lean_dec_ref_known(v_a_1776_, 0);
return v___x_1775_;
}
}
else
{
uint8_t v_contextDependent_1781_; 
v_contextDependent_1781_ = lean_ctor_get_uint8(v_a_1776_, sizeof(void*)*2 + 1);
if (v_contextDependent_1781_ == 0)
{
lean_dec_ref_known(v___x_1775_, 1);
goto v___jp_1777_;
}
else
{
lean_dec_ref_known(v_a_1776_, 2);
return v___x_1775_;
}
}
}
v___jp_1777_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1776_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
}
else
{
return v___x_1775_;
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v_argResults_1727_);
lean_dec_ref(v_mkNonRflResult_1723_);
v___x_1782_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_1728_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_argKinds_1722_ = stack[0].m_obj;
lean_object* v_mkNonRflResult_1723_ = stack[1].m_obj;
lean_object* v_e_1724_ = stack[2].m_obj;
lean_object* v_i_1725_ = stack[3].m_obj;
lean_object* v_numEqs_1726_ = stack[4].m_obj;
lean_object* v_argResults_1727_ = stack[5].m_obj;
uint8_t v_anyCD_1728_ = stack[6].m_num;
lean_object* v_a_1729_ = stack[7].m_obj;
lean_object* v_a_1730_ = stack[8].m_obj;
lean_object* v_a_1731_ = stack[9].m_obj;
lean_object* v_a_1732_ = stack[10].m_obj;
lean_object* v_a_1733_ = stack[11].m_obj;
lean_object* v_a_1734_ = stack[12].m_obj;
lean_object* v_a_1735_ = stack[13].m_obj;
lean_object* v_a_1736_ = stack[14].m_obj;
lean_object* v_a_1737_ = stack[15].m_obj;
lean_object* v_res_1784_;
v_res_1784_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1722_, v_mkNonRflResult_1723_, v_e_1724_, v_i_1725_, v_numEqs_1726_, v_argResults_1727_, v_anyCD_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
stack->m_obj
 = v_res_1784_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object** _args){
lean_object* v_argKinds_1785_ = _args[0];
lean_object* v_mkNonRflResult_1786_ = _args[1];
lean_object* v_e_1787_ = _args[2];
lean_object* v_i_1788_ = _args[3];
lean_object* v_numEqs_1789_ = _args[4];
lean_object* v_argResults_1790_ = _args[5];
lean_object* v_anyCD_1791_ = _args[6];
lean_object* v_a_1792_ = _args[7];
lean_object* v_a_1793_ = _args[8];
lean_object* v_a_1794_ = _args[9];
lean_object* v_a_1795_ = _args[10];
lean_object* v_a_1796_ = _args[11];
lean_object* v_a_1797_ = _args[12];
lean_object* v_a_1798_ = _args[13];
lean_object* v_a_1799_ = _args[14];
lean_object* v_a_1800_ = _args[15];
lean_object* v_a_1801_ = _args[16];
_start:
{
uint8_t v_anyCD_boxed_1802_; lean_object* v_res_1803_; 
v_anyCD_boxed_1802_ = lean_unbox(v_anyCD_1791_);
v_res_1803_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_1785_, v_mkNonRflResult_1786_, v_e_1787_, v_i_1788_, v_numEqs_1789_, v_argResults_1790_, v_anyCD_boxed_1802_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_argKinds_1785_);
return v_res_1803_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* v_msg_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_17247__overap_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
v___x_17247__overap_1816_ = lean_panic_fn_borrowed(v___x_1815_, v_msg_1804_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v___y_1807_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1805_);
v___x_1817_ = lean_apply_10(v___x_17247__overap_1816_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, lean_box(0));
return v___x_1817_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1804_ = stack[0].m_obj;
lean_object* v___y_1805_ = stack[1].m_obj;
lean_object* v___y_1806_ = stack[2].m_obj;
lean_object* v___y_1807_ = stack[3].m_obj;
lean_object* v___y_1808_ = stack[4].m_obj;
lean_object* v___y_1809_ = stack[5].m_obj;
lean_object* v___y_1810_ = stack[6].m_obj;
lean_object* v___y_1811_ = stack[7].m_obj;
lean_object* v___y_1812_ = stack[8].m_obj;
lean_object* v___y_1813_ = stack[9].m_obj;
lean_object* v_res_1818_;
v_res_1818_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
stack->m_obj
 = v_res_1818_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* v_msg_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
return v_res_1830_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(uint8_t v___x_1831_, lean_object* v_as_1832_, size_t v_i_1833_, size_t v_stop_1834_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_eq(v_i_1833_, v_stop_1834_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_array_uget_borrowed(v_as_1832_, v_i_1833_);
v___x_1841_ = lean_unbox(v___x_1840_);
if (v___x_1841_ == 3)
{
if (v___x_1831_ == 0)
{
goto v___jp_1835_;
}
else
{
return v___x_1831_;
}
}
else
{
goto v___jp_1835_;
}
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = 0;
return v___x_1842_;
}
v___jp_1835_:
{
size_t v___x_1836_; size_t v___x_1837_; 
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_add(v_i_1833_, v___x_1836_);
v_i_1833_ = v___x_1837_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1831_ = stack[0].m_num;
lean_object* v_as_1832_ = stack[1].m_obj;
size_t v_i_1833_ = stack[2].m_num;
size_t v_stop_1834_ = stack[3].m_num;
uint8_t v_res_1843_;
v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_1831_, v_as_1832_, v_i_1833_, v_stop_1834_);
stack->m_num = v_res_1843_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(lean_object* v___x_1844_, lean_object* v_as_1845_, lean_object* v_i_1846_, lean_object* v_stop_1847_){
_start:
{
uint8_t v___x_19083__boxed_1848_; size_t v_i_boxed_1849_; size_t v_stop_boxed_1850_; uint8_t v_res_1851_; lean_object* v_r_1852_; 
v___x_19083__boxed_1848_ = lean_unbox(v___x_1844_);
v_i_boxed_1849_ = lean_unbox_usize(v_i_1846_);
lean_dec(v_i_1846_);
v_stop_boxed_1850_ = lean_unbox_usize(v_stop_1847_);
lean_dec(v_stop_1847_);
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_19083__boxed_1848_, v_as_1845_, v_i_boxed_1849_, v_stop_boxed_1850_);
lean_dec_ref(v_as_1845_);
v_r_1852_ = lean_box(v_res_1851_);
return v_r_1852_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(lean_object* v_as_1853_, size_t v_i_1854_, size_t v_stop_1855_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_eq(v_i_1854_, v_stop_1855_);
if (v___x_1856_ == 0)
{
uint8_t v___x_1857_; uint8_t v___y_1859_; lean_object* v___x_1863_; 
v___x_1857_ = 1;
v___x_1863_ = lean_array_uget_borrowed(v_as_1853_, v_i_1854_);
if (lean_obj_tag(v___x_1863_) == 0)
{
uint8_t v_contextDependent_1864_; 
v_contextDependent_1864_ = lean_ctor_get_uint8(v___x_1863_, 1);
v___y_1859_ = v_contextDependent_1864_;
goto v___jp_1858_;
}
else
{
uint8_t v_contextDependent_1865_; 
v_contextDependent_1865_ = lean_ctor_get_uint8(v___x_1863_, sizeof(void*)*2 + 1);
v___y_1859_ = v_contextDependent_1865_;
goto v___jp_1858_;
}
v___jp_1858_:
{
if (v___y_1859_ == 0)
{
size_t v___x_1860_; size_t v___x_1861_; 
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_add(v_i_1854_, v___x_1860_);
v_i_1854_ = v___x_1861_;
goto _start;
}
else
{
return v___x_1857_;
}
}
}
else
{
uint8_t v___x_1866_; 
v___x_1866_ = 0;
return v___x_1866_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1853_ = stack[0].m_obj;
size_t v_i_1854_ = stack[1].m_num;
size_t v_stop_1855_ = stack[2].m_num;
uint8_t v_res_1867_;
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1853_, v_i_1854_, v_stop_1855_);
stack->m_num = v_res_1867_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* v_as_1868_, lean_object* v_i_1869_, lean_object* v_stop_1870_){
_start:
{
size_t v_i_boxed_1871_; size_t v_stop_boxed_1872_; uint8_t v_res_1873_; lean_object* v_r_1874_; 
v_i_boxed_1871_ = lean_unbox_usize(v_i_1869_);
lean_dec(v_i_1869_);
v_stop_boxed_1872_ = lean_unbox_usize(v_stop_1870_);
lean_dec(v_stop_1870_);
v_res_1873_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_1868_, v_i_boxed_1871_, v_stop_boxed_1872_);
lean_dec_ref(v_as_1868_);
v_r_1874_ = lean_box(v_res_1873_);
return v_r_1874_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1876_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_1877_ = lean_unsigned_to_nat(13u);
v___x_1878_ = lean_unsigned_to_nat(417u);
v___x_1879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_1881_ = l_mkPanicMessageWithDecl(v___x_1880_, v___x_1879_, v___x_1878_, v___x_1877_, v___x_1876_);
return v___x_1881_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* v_argResults_1882_, lean_object* v_as_1883_, size_t v_sz_1884_, size_t v_i_1885_, lean_object* v_b_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_a_1898_; uint8_t v___x_1902_; 
v___x_1902_ = lean_usize_dec_lt(v_i_1885_, v_sz_1884_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_b_1886_);
return v___x_1903_;
}
else
{
lean_object* v_snd_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_2099_; 
v_snd_1904_ = lean_ctor_get(v_b_1886_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_b_1886_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_b_1886_, 0);
lean_dec(v_unused_2100_);
v___x_1906_ = v_b_1886_;
v_isShared_1907_ = v_isSharedCheck_2099_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_snd_1904_);
lean_dec(v_b_1886_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_2099_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_snd_1908_; lean_object* v_snd_1909_; lean_object* v_snd_1910_; lean_object* v_snd_1911_; lean_object* v_fst_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_2097_; 
v_snd_1908_ = lean_ctor_get(v_snd_1904_, 1);
lean_inc(v_snd_1908_);
v_snd_1909_ = lean_ctor_get(v_snd_1908_, 1);
lean_inc(v_snd_1909_);
v_snd_1910_ = lean_ctor_get(v_snd_1909_, 1);
lean_inc(v_snd_1910_);
v_snd_1911_ = lean_ctor_get(v_snd_1910_, 1);
lean_inc(v_snd_1911_);
v_fst_1912_ = lean_ctor_get(v_snd_1904_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_snd_1904_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v_snd_1904_, 1);
lean_dec(v_unused_2098_);
v___x_1914_ = v_snd_1904_;
v_isShared_1915_ = v_isSharedCheck_2097_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_fst_1912_);
lean_dec(v_snd_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_2097_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_fst_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_2095_; 
v_fst_1916_ = lean_ctor_get(v_snd_1908_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_snd_1908_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v_snd_1908_, 1);
lean_dec(v_unused_2096_);
v___x_1918_ = v_snd_1908_;
v_isShared_1919_ = v_isSharedCheck_2095_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_fst_1916_);
lean_dec(v_snd_1908_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_2095_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_fst_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_2093_; 
v_fst_1920_ = lean_ctor_get(v_snd_1909_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_snd_1909_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_snd_1909_, 1);
lean_dec(v_unused_2094_);
v___x_1922_ = v_snd_1909_;
v_isShared_1923_ = v_isSharedCheck_2093_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_fst_1920_);
lean_dec(v_snd_1909_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_2093_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_fst_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_2091_; 
v_fst_1924_ = lean_ctor_get(v_snd_1910_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_snd_1910_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v_snd_1910_, 1);
lean_dec(v_unused_2092_);
v___x_1926_ = v_snd_1910_;
v_isShared_1927_ = v_isSharedCheck_2091_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_fst_1924_);
lean_dec(v_snd_1910_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_2091_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_array_1928_; lean_object* v_start_1929_; lean_object* v_stop_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_array_1928_ = lean_ctor_get(v_snd_1911_, 0);
v_start_1929_ = lean_ctor_get(v_snd_1911_, 1);
v_stop_1930_ = lean_ctor_get(v_snd_1911_, 2);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_nat_dec_lt(v_start_1929_, v_stop_1930_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1934_; 
if (v_isShared_1927_ == 0)
{
v___x_1934_ = v___x_1926_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_fst_1924_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_snd_1911_);
v___x_1934_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1934_);
v___x_1936_ = v___x_1922_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_fst_1920_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1936_);
v___x_1938_ = v___x_1918_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_fst_1916_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1938_);
v___x_1940_ = v___x_1914_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_fst_1912_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1940_);
lean_ctor_set(v___x_1906_, 0, v___x_1931_);
v___x_1942_ = v___x_1906_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
}
}
}
}
else
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2087_; 
lean_inc(v_stop_1930_);
lean_inc(v_start_1929_);
lean_inc_ref(v_array_1928_);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_snd_1911_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; lean_object* v_unused_2089_; lean_object* v_unused_2090_; 
v_unused_2088_ = lean_ctor_get(v_snd_1911_, 2);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_snd_1911_, 1);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_snd_1911_, 0);
lean_dec(v_unused_2090_);
v___x_1950_ = v_snd_1911_;
v_isShared_1951_ = v_isSharedCheck_2087_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v_snd_1911_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2087_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v_a_1952_ = lean_array_uget_borrowed(v_as_1883_, v_i_1885_);
v___x_1953_ = lean_array_fget(v_array_1928_, v_start_1929_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_add(v_start_1929_, v___x_1954_);
lean_dec(v_start_1929_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___x_1955_);
v___x_1957_ = v___x_1950_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_array_1928_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_stop_1930_);
v___x_1957_ = v_reuseFailAlloc_2086_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v_proof_1961_; lean_object* v_subst_1962_; uint8_t v___x_1988_; 
lean_inc(v_a_1952_);
v___x_1958_ = l_Lean_Expr_app___override(v_fst_1912_, v_a_1952_);
v___x_1959_ = l_Lean_Expr_bindingBody_x21(v_fst_1916_);
lean_dec(v_fst_1916_);
v___x_1988_ = lean_unbox(v___x_1953_);
lean_dec(v___x_1953_);
switch(v___x_1988_)
{
case 0:
{
lean_del_object(v___x_1926_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_del_object(v___x_1914_);
lean_del_object(v___x_1906_);
goto v___jp_1981_;
}
case 3:
{
lean_del_object(v___x_1926_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_del_object(v___x_1914_);
lean_del_object(v___x_1906_);
goto v___jp_1981_;
}
case 5:
{
lean_object* v___x_1989_; lean_object* v_instNew_1991_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_del_object(v___x_1926_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_del_object(v___x_1914_);
lean_del_object(v___x_1906_);
lean_inc_n(v_a_1952_, 2);
v___x_1989_ = lean_array_push(v_fst_1924_, v_a_1952_);
v___x_2000_ = l_Lean_Expr_bindingDomain_x21(v___x_1959_);
v___x_2001_ = lean_expr_instantiate_rev(v___x_2000_, v___x_1989_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = l_Lean_Meta_Sym_inferType(v_a_1952_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
lean_inc_ref(v___x_2001_);
v___x_2004_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_a_2003_, v___x_2001_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; uint8_t v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = lean_unbox(v_a_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Meta_trySynthInstance(v___x_2001_, v___x_1931_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2025_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2025_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2025_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_a_2008_) == 1)
{
lean_object* v_a_2012_; 
lean_del_object(v___x_2010_);
lean_dec(v_a_2005_);
v_a_2012_ = lean_ctor_get(v_a_2008_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v_a_2008_, 1);
v_instNew_1991_ = v_a_2012_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2013_; uint8_t v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_dec(v_a_2008_);
v___x_2013_ = lean_alloc_ctor(0, 0, 2);
v___x_2014_ = lean_unbox(v_a_2005_);
lean_ctor_set_uint8(v___x_2013_, 0, v___x_2014_);
v___x_2015_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
lean_ctor_set_uint8(v___x_2013_, 1, v___x_2015_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2013_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_1989_);
lean_ctor_set(v___x_2017_, 1, v___x_1957_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_fst_1920_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_1959_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_1958_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2016_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2021_);
v___x_2023_ = v___x_2010_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_a_2005_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1957_);
lean_dec(v_fst_1920_);
v_a_2026_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2007_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2007_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_dec(v_a_2005_);
lean_dec_ref(v___x_2001_);
lean_inc(v_a_1952_);
v_instNew_1991_ = v_a_1952_;
goto v___jp_1990_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v___x_2001_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1957_);
lean_dec(v_fst_1920_);
v_a_2034_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2004_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2004_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v___x_2001_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1957_);
lean_dec(v_fst_1920_);
v_a_2042_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2002_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2002_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
v___jp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v_instNew_1991_);
v___x_1992_ = l_Lean_Expr_app___override(v___x_1958_, v_instNew_1991_);
v___x_1993_ = lean_array_push(v___x_1989_, v_instNew_1991_);
v___x_1994_ = l_Lean_Expr_bindingBody_x21(v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1957_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_fst_1920_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1994_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1992_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1931_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v_a_1898_ = v___x_1999_;
goto v___jp_1897_;
}
}
case 2:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(v_a_1952_);
v___x_2051_ = lean_array_push(v_fst_1924_, v_a_1952_);
v___x_2052_ = lean_array_get_borrowed(v___x_2050_, v_argResults_1882_, v_fst_1920_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v___x_2053_; 
lean_inc(v_a_1952_);
v___x_2053_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1952_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_n(v_a_2054_, 2);
lean_dec_ref_known(v___x_2053_, 1);
lean_inc_n(v_a_1952_, 2);
v___x_2055_ = l_Lean_mkAppB(v___x_1958_, v_a_1952_, v_a_2054_);
v___x_2056_ = lean_array_push(v___x_2051_, v_a_1952_);
v___x_2057_ = lean_array_push(v___x_2056_, v_a_2054_);
v_proof_1961_ = v___x_2055_;
v_subst_1962_ = v___x_2057_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v___x_2051_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1926_);
lean_del_object(v___x_1922_);
lean_dec(v_fst_1920_);
lean_del_object(v___x_1918_);
lean_del_object(v___x_1914_);
lean_del_object(v___x_1906_);
v_a_2058_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2053_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2053_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_e_x27_2066_; lean_object* v_proof_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_e_x27_2066_ = lean_ctor_get(v___x_2052_, 0);
v_proof_2067_ = lean_ctor_get(v___x_2052_, 1);
lean_inc_ref_n(v_proof_2067_, 2);
lean_inc_ref_n(v_e_x27_2066_, 2);
v___x_2068_ = l_Lean_mkAppB(v___x_1958_, v_e_x27_2066_, v_proof_2067_);
v___x_2069_ = lean_array_push(v___x_2051_, v_e_x27_2066_);
v___x_2070_ = lean_array_push(v___x_2069_, v_proof_2067_);
v_proof_1961_ = v___x_2068_;
v_subst_1962_ = v___x_2070_;
goto v___jp_1960_;
}
}
default: 
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_del_object(v___x_1926_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_del_object(v___x_1914_);
lean_del_object(v___x_1906_);
v___x_2071_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
v___x_2072_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_2071_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref_known(v___x_2072_, 1);
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_fst_1924_);
lean_ctor_set(v___x_2073_, 1, v___x_1957_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_fst_1920_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_1959_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_1958_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_1931_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v_a_1898_ = v___x_2077_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1957_);
lean_dec(v_fst_1924_);
lean_dec(v_fst_1920_);
v_a_2078_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2072_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2072_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1963_ = l_Lean_Expr_bindingBody_x21(v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1964_ = l_Lean_Expr_bindingBody_x21(v___x_1963_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = lean_nat_add(v_fst_1920_, v___x_1954_);
lean_dec(v_fst_1920_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___x_1957_);
lean_ctor_set(v___x_1926_, 0, v_subst_1962_);
v___x_1967_ = v___x_1926_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_subst_1962_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___x_1957_);
v___x_1967_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1967_);
lean_ctor_set(v___x_1922_, 0, v___x_1965_);
v___x_1969_ = v___x_1922_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1969_);
lean_ctor_set(v___x_1918_, 0, v___x_1964_);
v___x_1971_ = v___x_1918_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1971_);
lean_ctor_set(v___x_1914_, 0, v_proof_1961_);
v___x_1973_ = v___x_1914_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_proof_1961_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1973_);
lean_ctor_set(v___x_1906_, 0, v___x_1931_);
v___x_1975_ = v___x_1906_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
v_a_1898_ = v___x_1975_;
goto v___jp_1897_;
}
}
}
}
}
}
v___jp_1981_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_inc(v_a_1952_);
v___x_1982_ = lean_array_push(v_fst_1924_, v_a_1952_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1957_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_fst_1920_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1959_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1958_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1931_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v_a_1898_ = v___x_1987_;
goto v___jp_1897_;
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
v___jp_1897_:
{
size_t v___x_1899_; size_t v___x_1900_; 
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_add(v_i_1885_, v___x_1899_);
v_i_1885_ = v___x_1900_;
v_b_1886_ = v_a_1898_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_argResults_1882_ = stack[0].m_obj;
lean_object* v_as_1883_ = stack[1].m_obj;
size_t v_sz_1884_ = stack[2].m_num;
size_t v_i_1885_ = stack[3].m_num;
lean_object* v_b_1886_ = stack[4].m_obj;
lean_object* v___y_1887_ = stack[5].m_obj;
lean_object* v___y_1888_ = stack[6].m_obj;
lean_object* v___y_1889_ = stack[7].m_obj;
lean_object* v___y_1890_ = stack[8].m_obj;
lean_object* v___y_1891_ = stack[9].m_obj;
lean_object* v___y_1892_ = stack[10].m_obj;
lean_object* v___y_1893_ = stack[11].m_obj;
lean_object* v___y_1894_ = stack[12].m_obj;
lean_object* v___y_1895_ = stack[13].m_obj;
lean_object* v_res_2101_;
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_1882_, v_as_1883_, v_sz_1884_, v_i_1885_, v_b_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
stack->m_obj
 = v_res_2101_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* v_argResults_2102_, lean_object* v_as_2103_, lean_object* v_sz_2104_, lean_object* v_i_2105_, lean_object* v_b_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
size_t v_sz_boxed_2117_; size_t v_i_boxed_2118_; lean_object* v_res_2119_; 
v_sz_boxed_2117_ = lean_unbox_usize(v_sz_2104_);
lean_dec(v_sz_2104_);
v_i_boxed_2118_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_2102_, v_as_2103_, v_sz_boxed_2117_, v_i_boxed_2118_, v_b_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v_as_2103_);
lean_dec_ref(v_argResults_2102_);
return v_res_2119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2121_ = lean_unsigned_to_nat(34u);
v___x_2122_ = lean_unsigned_to_nat(418u);
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2125_ = l_mkPanicMessageWithDecl(v___x_2124_, v___x_2123_, v___x_2122_, v___x_2121_, v___x_2120_);
return v___x_2125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2128_; lean_object* v_dummy_2129_; 
v___x_2128_ = lean_box(0);
v_dummy_2129_ = l_Lean_Expr_sort___override(v___x_2128_);
return v_dummy_2129_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* v_e_2133_, lean_object* v_argKinds_2134_, lean_object* v_type_2135_, lean_object* v_proof_2136_, lean_object* v_argResults_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_j_2151_; lean_object* v_subst_2152_; lean_object* v_dummy_2153_; lean_object* v_nargs_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_args_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; size_t v_sz_2167_; size_t v___x_2168_; lean_object* v___x_2169_; 
v_j_2151_ = lean_unsigned_to_nat(0u);
v_subst_2152_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1));
v_dummy_2153_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
v_nargs_2154_ = l_Lean_Expr_getAppNumArgs(v_e_2133_);
lean_inc(v_nargs_2154_);
v___x_2155_ = lean_mk_array(v_nargs_2154_, v_dummy_2153_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_sub(v_nargs_2154_, v___x_2156_);
lean_dec(v_nargs_2154_);
v_args_2158_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2133_, v___x_2155_, v___x_2157_);
v___x_2159_ = lean_array_get_size(v_argKinds_2134_);
lean_inc_ref(v_argKinds_2134_);
v___x_2160_ = l_Array_toSubarray___redArg(v_argKinds_2134_, v_j_2151_, v___x_2159_);
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v_subst_2152_);
lean_ctor_set(v___x_2162_, 1, v___x_2160_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v_j_2151_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_type_2135_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_proof_2136_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2161_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v_sz_2167_ = lean_array_size(v_args_2158_);
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_2137_, v_args_2158_, v_sz_2167_, v___x_2168_, v___x_2166_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec_ref(v_args_2158_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2240_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2240_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2240_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_fst_2174_; 
v_fst_2174_ = lean_ctor_get(v_a_2170_, 0);
if (lean_obj_tag(v_fst_2174_) == 0)
{
lean_object* v_snd_2175_; lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___y_2179_; uint8_t v___y_2180_; lean_object* v_rhs_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v_fst_2208_; lean_object* v_snd_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_snd_2175_ = lean_ctor_get(v_a_2170_, 1);
lean_inc(v_snd_2175_);
lean_dec(v_a_2170_);
v_fst_2176_ = lean_ctor_get(v_snd_2175_, 0);
lean_inc(v_fst_2176_);
v_snd_2177_ = lean_ctor_get(v_snd_2175_, 1);
lean_inc(v_snd_2177_);
lean_dec(v_snd_2175_);
v_fst_2208_ = lean_ctor_get(v_snd_2177_, 0);
lean_inc(v_fst_2208_);
v_snd_2209_ = lean_ctor_get(v_snd_2177_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_snd_2177_);
v___x_2210_ = l_Lean_Expr_cleanupAnnotations(v_fst_2208_);
v___x_2211_ = l_Lean_Expr_isApp(v___x_2210_);
if (v___x_2211_ == 0)
{
lean_dec_ref(v___x_2210_);
lean_dec(v_snd_2209_);
lean_dec(v_fst_2176_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_argKinds_2134_);
goto v___jp_2148_;
}
else
{
lean_object* v_arg_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_arg_2212_ = lean_ctor_get(v___x_2210_, 1);
lean_inc_ref(v_arg_2212_);
v___x_2213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2210_);
v___x_2214_ = l_Lean_Expr_isApp(v___x_2213_);
if (v___x_2214_ == 0)
{
lean_dec_ref(v___x_2213_);
lean_dec_ref(v_arg_2212_);
lean_dec(v_snd_2209_);
lean_dec(v_fst_2176_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_argKinds_2134_);
goto v___jp_2148_;
}
else
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2213_);
v___x_2216_ = l_Lean_Expr_isApp(v___x_2215_);
if (v___x_2216_ == 0)
{
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_arg_2212_);
lean_dec(v_snd_2209_);
lean_dec(v_fst_2176_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_argKinds_2134_);
goto v___jp_2148_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2215_);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
v___x_2219_ = l_Lean_Expr_isConstOf(v___x_2217_, v___x_2218_);
lean_dec_ref(v___x_2217_);
if (v___x_2219_ == 0)
{
lean_dec_ref(v_arg_2212_);
lean_dec(v_snd_2209_);
lean_dec(v_fst_2176_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_argKinds_2134_);
goto v___jp_2148_;
}
else
{
lean_object* v_snd_2220_; lean_object* v_fst_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_snd_2220_ = lean_ctor_get(v_snd_2209_, 1);
lean_inc(v_snd_2220_);
lean_dec(v_snd_2209_);
v_fst_2221_ = lean_ctor_get(v_snd_2220_, 0);
lean_inc(v_fst_2221_);
lean_dec(v_snd_2220_);
v___x_2222_ = lean_expr_instantiate_rev(v_arg_2212_, v_fst_2221_);
lean_dec(v_fst_2221_);
lean_dec_ref(v_arg_2212_);
v___x_2223_ = lean_nat_dec_lt(v_j_2151_, v___x_2159_);
if (v___x_2223_ == 0)
{
lean_dec_ref(v_argKinds_2134_);
v_rhs_2187_ = v___x_2222_;
v___y_2188_ = v___y_2141_;
v___y_2189_ = v___y_2142_;
v___y_2190_ = v___y_2143_;
v___y_2191_ = v___y_2144_;
v___y_2192_ = v___y_2145_;
v___y_2193_ = v___y_2146_;
goto v___jp_2186_;
}
else
{
if (v___x_2223_ == 0)
{
lean_dec_ref(v_argKinds_2134_);
v_rhs_2187_ = v___x_2222_;
v___y_2188_ = v___y_2141_;
v___y_2189_ = v___y_2142_;
v___y_2190_ = v___y_2143_;
v___y_2191_ = v___y_2144_;
v___y_2192_ = v___y_2145_;
v___y_2193_ = v___y_2146_;
goto v___jp_2186_;
}
else
{
size_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = lean_usize_of_nat(v___x_2159_);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_2219_, v_argKinds_2134_, v___x_2168_, v___x_2224_);
lean_dec_ref(v_argKinds_2134_);
if (v___x_2225_ == 0)
{
v_rhs_2187_ = v___x_2222_;
v___y_2188_ = v___y_2141_;
v___y_2189_ = v___y_2142_;
v___y_2190_ = v___y_2143_;
v___y_2191_ = v___y_2144_;
v___y_2192_ = v___y_2145_;
v___y_2193_ = v___y_2146_;
goto v___jp_2186_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_Meta_Simp_removeUnnecessaryCasts(v___x_2222_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v_rhs_2187_ = v_a_2227_;
v___y_2188_ = v___y_2141_;
v___y_2189_ = v___y_2142_;
v___y_2190_ = v___y_2143_;
v___y_2191_ = v___y_2144_;
v___y_2192_ = v___y_2145_;
v___y_2193_ = v___y_2146_;
goto v___jp_2186_;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_fst_2176_);
lean_del_object(v___x_2172_);
v_a_2228_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
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
v___jp_2178_:
{
uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2181_ = 0;
v___x_2182_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2182_, 0, v___y_2179_);
lean_ctor_set(v___x_2182_, 1, v_fst_2176_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*2, v___x_2181_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*2 + 1, v___y_2180_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2182_);
v___x_2184_ = v___x_2172_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
v___jp_2186_:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_Sym_shareCommonInc(v_rhs_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = lean_array_get_size(v_argResults_2137_);
v___x_2197_ = lean_nat_dec_lt(v_j_2151_, v___x_2196_);
if (v___x_2197_ == 0)
{
v___y_2179_ = v_a_2195_;
v___y_2180_ = v___x_2197_;
goto v___jp_2178_;
}
else
{
if (v___x_2197_ == 0)
{
v___y_2179_ = v_a_2195_;
v___y_2180_ = v___x_2197_;
goto v___jp_2178_;
}
else
{
size_t v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_usize_of_nat(v___x_2196_);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_2137_, v___x_2168_, v___x_2198_);
v___y_2179_ = v_a_2195_;
v___y_2180_ = v___x_2199_;
goto v___jp_2178_;
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_fst_2176_);
lean_del_object(v___x_2172_);
v_a_2200_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2194_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2194_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2238_; 
lean_inc_ref(v_fst_2174_);
lean_dec(v_a_2170_);
lean_dec_ref(v_argKinds_2134_);
v_val_2236_ = lean_ctor_get(v_fst_2174_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v_fst_2174_, 1);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v_val_2236_);
v___x_2238_ = v___x_2172_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_val_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v_argKinds_2134_);
v_a_2241_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2169_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2169_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
v___jp_2148_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
v___x_2150_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2149_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2150_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2133_ = stack[0].m_obj;
lean_object* v_argKinds_2134_ = stack[1].m_obj;
lean_object* v_type_2135_ = stack[2].m_obj;
lean_object* v_proof_2136_ = stack[3].m_obj;
lean_object* v_argResults_2137_ = stack[4].m_obj;
lean_object* v___y_2138_ = stack[5].m_obj;
lean_object* v___y_2139_ = stack[6].m_obj;
lean_object* v___y_2140_ = stack[7].m_obj;
lean_object* v___y_2141_ = stack[8].m_obj;
lean_object* v___y_2142_ = stack[9].m_obj;
lean_object* v___y_2143_ = stack[10].m_obj;
lean_object* v___y_2144_ = stack[11].m_obj;
lean_object* v___y_2145_ = stack[12].m_obj;
lean_object* v___y_2146_ = stack[13].m_obj;
lean_object* v_res_2249_;
v_res_2249_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2133_, v_argKinds_2134_, v_type_2135_, v_proof_2136_, v_argResults_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
stack->m_obj
 = v_res_2249_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* v_e_2250_, lean_object* v_argKinds_2251_, lean_object* v_type_2252_, lean_object* v_proof_2253_, lean_object* v_argResults_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(v_e_2250_, v_argKinds_2251_, v_type_2252_, v_proof_2253_, v_argResults_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v_argResults_2254_);
return v_res_2265_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t v___x_2266_, lean_object* v_x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2278_, 0, v___x_2266_);
lean_ctor_set_uint8(v___x_2278_, 1, v___x_2266_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2266_ = stack[0].m_num;
lean_object* v_x_2267_ = stack[1].m_obj;
lean_object* v___y_2268_ = stack[2].m_obj;
lean_object* v___y_2269_ = stack[3].m_obj;
lean_object* v___y_2270_ = stack[4].m_obj;
lean_object* v___y_2271_ = stack[5].m_obj;
lean_object* v___y_2272_ = stack[6].m_obj;
lean_object* v___y_2273_ = stack[7].m_obj;
lean_object* v___y_2274_ = stack[8].m_obj;
lean_object* v___y_2275_ = stack[9].m_obj;
lean_object* v___y_2276_ = stack[10].m_obj;
lean_object* v_res_2280_;
v_res_2280_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_2266_, v_x_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
stack->m_obj
 = v_res_2280_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* v___x_2281_, lean_object* v_x_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v___x_20150__boxed_2293_; lean_object* v_res_2294_; 
v___x_20150__boxed_2293_ = lean_unbox(v___x_2281_);
v_res_2294_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(v___x_20150__boxed_2293_, v_x_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v_x_2282_);
return v_res_2294_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* v___x_2297_, lean_object* v_argKinds_2298_, lean_object* v_mkNonRflResult_2299_, lean_object* v_x_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = lean_nat_sub(v___x_2297_, v___x_2311_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2315_ = 0;
v___x_2316_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2298_, v_mkNonRflResult_2299_, v_x_2300_, v___x_2312_, v___x_2313_, v___x_2314_, v___x_2315_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2316_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2297_ = stack[0].m_obj;
lean_object* v_argKinds_2298_ = stack[1].m_obj;
lean_object* v_mkNonRflResult_2299_ = stack[2].m_obj;
lean_object* v_x_2300_ = stack[3].m_obj;
lean_object* v___y_2301_ = stack[4].m_obj;
lean_object* v___y_2302_ = stack[5].m_obj;
lean_object* v___y_2303_ = stack[6].m_obj;
lean_object* v___y_2304_ = stack[7].m_obj;
lean_object* v___y_2305_ = stack[8].m_obj;
lean_object* v___y_2306_ = stack[9].m_obj;
lean_object* v___y_2307_ = stack[10].m_obj;
lean_object* v___y_2308_ = stack[11].m_obj;
lean_object* v___y_2309_ = stack[12].m_obj;
lean_object* v_res_2317_;
v_res_2317_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2297_, v_argKinds_2298_, v_mkNonRflResult_2299_, v_x_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
stack->m_obj
 = v_res_2317_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* v___x_2318_, lean_object* v_argKinds_2319_, lean_object* v_mkNonRflResult_2320_, lean_object* v_x_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(v___x_2318_, v_argKinds_2319_, v_mkNonRflResult_2320_, v_x_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v_argKinds_2319_);
lean_dec(v___x_2318_);
return v_res_2332_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* v_e_2333_, lean_object* v_thm_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_type_2345_; lean_object* v_proof_2346_; lean_object* v_argKinds_2347_; lean_object* v_mkNonRflResult_2348_; lean_object* v_numArgs_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_type_2345_ = lean_ctor_get(v_thm_2334_, 0);
lean_inc_ref(v_type_2345_);
v_proof_2346_ = lean_ctor_get(v_thm_2334_, 1);
lean_inc_ref(v_proof_2346_);
v_argKinds_2347_ = lean_ctor_get(v_thm_2334_, 2);
lean_inc_ref_n(v_argKinds_2347_, 2);
lean_dec_ref(v_thm_2334_);
lean_inc_ref(v_e_2333_);
v_mkNonRflResult_2348_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(v_mkNonRflResult_2348_, 0, v_e_2333_);
lean_closure_set(v_mkNonRflResult_2348_, 1, v_argKinds_2347_);
lean_closure_set(v_mkNonRflResult_2348_, 2, v_type_2345_);
lean_closure_set(v_mkNonRflResult_2348_, 3, v_proof_2346_);
v_numArgs_2349_ = l_Lean_Expr_getAppNumArgs(v_e_2333_);
v___x_2350_ = lean_array_get_size(v_argKinds_2347_);
v___x_2351_ = lean_nat_dec_lt(v___x_2350_, v_numArgs_2349_);
if (v___x_2351_ == 0)
{
uint8_t v___x_2352_; 
v___x_2352_ = lean_nat_dec_lt(v_numArgs_2349_, v___x_2350_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v_numArgs_2349_);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_sub(v___x_2350_, v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0));
v___x_2357_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_2347_, v_mkNonRflResult_2348_, v_e_2333_, v___x_2354_, v___x_2355_, v___x_2356_, v___x_2352_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec_ref(v_argKinds_2347_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
lean_dec_ref(v_mkNonRflResult_2348_);
lean_dec_ref(v_argKinds_2347_);
v___x_2358_ = lean_box(v___x_2351_);
v___f_2359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(v___f_2359_, 0, v___x_2358_);
v___x_2360_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2359_, v_e_2333_, v_numArgs_2349_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec(v_numArgs_2349_);
return v___x_2360_;
}
}
else
{
lean_object* v___f_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___f_2361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2361_, 0, v___x_2350_);
lean_closure_set(v___f_2361_, 1, v_argKinds_2347_);
lean_closure_set(v___f_2361_, 2, v_mkNonRflResult_2348_);
v___x_2362_ = lean_nat_sub(v_numArgs_2349_, v___x_2350_);
lean_dec(v_numArgs_2349_);
v___x_2363_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v___f_2361_, v_e_2333_, v___x_2362_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec(v___x_2362_);
return v___x_2363_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2333_ = stack[0].m_obj;
lean_object* v_thm_2334_ = stack[1].m_obj;
lean_object* v_a_2335_ = stack[2].m_obj;
lean_object* v_a_2336_ = stack[3].m_obj;
lean_object* v_a_2337_ = stack[4].m_obj;
lean_object* v_a_2338_ = stack[5].m_obj;
lean_object* v_a_2339_ = stack[6].m_obj;
lean_object* v_a_2340_ = stack[7].m_obj;
lean_object* v_a_2341_ = stack[8].m_obj;
lean_object* v_a_2342_ = stack[9].m_obj;
lean_object* v_a_2343_ = stack[10].m_obj;
lean_object* v_res_2364_;
v_res_2364_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2333_, v_thm_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
stack->m_obj
 = v_res_2364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* v_e_2365_, lean_object* v_thm_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2365_, v_thm_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
return v_res_2377_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* v_e_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_f_2389_; lean_object* v___x_2390_; 
v_f_2389_ = l_Lean_Expr_getAppFn(v_e_2378_);
v___x_2390_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_2389_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2406_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2406_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2406_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
switch(lean_obj_tag(v_a_2391_))
{
case 0:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec_ref(v_e_2378_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
case 1:
{
lean_object* v_prefixSize_2399_; lean_object* v_suffixSize_2400_; lean_object* v___x_2401_; 
lean_del_object(v___x_2393_);
v_prefixSize_2399_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_prefixSize_2399_);
v_suffixSize_2400_ = lean_ctor_get(v_a_2391_, 1);
lean_inc(v_suffixSize_2400_);
lean_dec_ref_known(v_a_2391_, 2);
v___x_2401_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(v_e_2378_, v_prefixSize_2399_, v_suffixSize_2400_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_prefixSize_2399_);
return v___x_2401_;
}
case 2:
{
lean_object* v_rewritable_2402_; lean_object* v___x_2403_; 
lean_del_object(v___x_2393_);
v_rewritable_2402_ = lean_ctor_get(v_a_2391_, 0);
lean_inc_ref(v_rewritable_2402_);
lean_dec_ref_known(v_a_2391_, 1);
v___x_2403_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_e_2378_, v_rewritable_2402_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2403_;
}
default: 
{
lean_object* v_thm_2404_; lean_object* v___x_2405_; 
lean_del_object(v___x_2393_);
v_thm_2404_ = lean_ctor_get(v_a_2391_, 0);
lean_inc_ref(v_thm_2404_);
lean_dec_ref_known(v_a_2391_, 1);
v___x_2405_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_2378_, v_thm_2404_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v_e_2378_);
v_a_2407_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2390_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2390_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpAppArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2378_ = stack[0].m_obj;
lean_object* v_a_2379_ = stack[1].m_obj;
lean_object* v_a_2380_ = stack[2].m_obj;
lean_object* v_a_2381_ = stack[3].m_obj;
lean_object* v_a_2382_ = stack[4].m_obj;
lean_object* v_a_2383_ = stack[5].m_obj;
lean_object* v_a_2384_ = stack[6].m_obj;
lean_object* v_a_2385_ = stack[7].m_obj;
lean_object* v_a_2386_ = stack[8].m_obj;
lean_object* v_a_2387_ = stack[9].m_obj;
lean_object* v_res_2415_;
v_res_2415_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
stack->m_obj
 = v_res_2415_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* v_e_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
return v_res_2427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2429_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2430_ = lean_unsigned_to_nat(55u);
v___x_2431_ = lean_unsigned_to_nat(505u);
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2434_ = l_mkPanicMessageWithDecl(v___x_2433_, v___x_2432_, v___x_2431_, v___x_2430_, v___x_2429_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
v___x_2436_ = lean_unsigned_to_nat(11u);
v___x_2437_ = lean_unsigned_to_nat(513u);
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2440_ = l_mkPanicMessageWithDecl(v___x_2439_, v___x_2438_, v___x_2437_, v___x_2436_, v___x_2435_);
return v___x_2440_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* v_stop_2441_, lean_object* v_e_2442_, lean_object* v_i_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
uint8_t v_cd_2455_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = lean_unsigned_to_nat(0u);
v___x_2459_ = lean_nat_dec_eq(v_i_2443_, v___x_2458_);
if (v___x_2459_ == 0)
{
if (lean_obj_tag(v_e_2442_) == 5)
{
lean_object* v_fn_2460_; lean_object* v_arg_2461_; lean_object* v___x_2462_; lean_object* v_i_2463_; lean_object* v___x_2464_; 
v_fn_2460_ = lean_ctor_get(v_e_2442_, 0);
lean_inc_ref_n(v_fn_2460_, 2);
v_arg_2461_ = lean_ctor_get(v_e_2442_, 1);
lean_inc_ref(v_arg_2461_);
v___x_2462_ = lean_unsigned_to_nat(1u);
v_i_2463_ = lean_nat_sub(v_i_2443_, v___x_2462_);
v___x_2464_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2441_, v_fn_2460_, v_i_2463_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; uint8_t v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = lean_nat_dec_lt(v_i_2463_, v_stop_2441_);
lean_dec(v_i_2463_);
if (v___x_2466_ == 0)
{
if (lean_obj_tag(v_a_2465_) == 0)
{
uint8_t v_contextDependent_2467_; 
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
v_contextDependent_2467_ = lean_ctor_get_uint8(v_a_2465_, 1);
lean_dec_ref_known(v_a_2465_, 0);
v_cd_2455_ = v_contextDependent_2467_;
goto v___jp_2454_;
}
else
{
lean_object* v_e_x27_2468_; lean_object* v_proof_2469_; uint8_t v_contextDependent_2470_; lean_object* v___x_2471_; 
v_e_x27_2468_ = lean_ctor_get(v_a_2465_, 0);
lean_inc_ref(v_e_x27_2468_);
v_proof_2469_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_proof_2469_);
v_contextDependent_2470_ = lean_ctor_get_uint8(v_a_2465_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2465_, 2);
v___x_2471_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2442_, v_fn_2460_, v_arg_2461_, v_e_x27_2468_, v_proof_2469_, v___x_2459_, v_contextDependent_2470_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2471_;
}
}
else
{
lean_object* v___x_2472_; 
lean_inc_ref(v_fn_2460_);
v___x_2472_ = l_Lean_Meta_Sym_inferType(v_fn_2460_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = l_Lean_Meta_whnfD(v_a_2473_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
if (lean_obj_tag(v_a_2475_) == 7)
{
lean_object* v_binderType_2476_; lean_object* v_body_2477_; uint8_t v___x_2478_; 
v_binderType_2476_ = lean_ctor_get(v_a_2475_, 1);
lean_inc_ref(v_binderType_2476_);
v_body_2477_ = lean_ctor_get(v_a_2475_, 2);
lean_inc_ref(v_body_2477_);
lean_dec_ref_known(v_a_2475_, 3);
v___x_2478_ = l_Lean_Expr_hasLooseBVars(v_body_2477_);
lean_dec_ref(v_body_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Meta_isProp(v_binderType_2476_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; uint8_t v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2481_ = lean_unbox(v_a_2480_);
lean_dec(v_a_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
lean_inc(v_a_2452_);
lean_inc_ref(v_a_2451_);
lean_inc(v_a_2450_);
lean_inc_ref(v_a_2449_);
lean_inc(v_a_2448_);
lean_inc_ref(v_a_2447_);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_arg_2461_);
v___x_2482_ = lean_sym_simp(v_arg_2461_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2442_, v_fn_2460_, v_arg_2461_, v_a_2465_, v_a_2483_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2484_;
}
else
{
lean_dec(v_a_2465_);
lean_dec_ref(v_arg_2461_);
lean_dec_ref_known(v_e_2442_, 2);
lean_dec_ref(v_fn_2460_);
return v___x_2482_;
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2485_, 0, v___x_2459_);
lean_ctor_set_uint8(v___x_2485_, 1, v___x_2459_);
v___x_2486_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_e_2442_, v_fn_2460_, v_arg_2461_, v_a_2465_, v___x_2485_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2486_;
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2465_);
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
v_a_2487_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2479_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2479_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_2476_);
if (lean_obj_tag(v_a_2465_) == 0)
{
uint8_t v_contextDependent_2495_; 
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
v_contextDependent_2495_ = lean_ctor_get_uint8(v_a_2465_, 1);
lean_dec_ref_known(v_a_2465_, 0);
v_cd_2455_ = v_contextDependent_2495_;
goto v___jp_2454_;
}
else
{
lean_object* v_e_x27_2496_; lean_object* v_proof_2497_; uint8_t v_contextDependent_2498_; lean_object* v___x_2499_; 
v_e_x27_2496_ = lean_ctor_get(v_a_2465_, 0);
lean_inc_ref(v_e_x27_2496_);
v_proof_2497_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_proof_2497_);
v_contextDependent_2498_ = lean_ctor_get_uint8(v_a_2465_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2465_, 2);
v___x_2499_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_2442_, v_fn_2460_, v_arg_2461_, v_e_x27_2496_, v_proof_2497_, v___x_2459_, v_contextDependent_2498_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2499_;
}
}
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v_a_2475_);
lean_dec(v_a_2465_);
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
v___x_2500_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
v___x_2501_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2500_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2501_;
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec(v_a_2465_);
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
v_a_2502_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2474_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2474_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_a_2465_);
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
v_a_2510_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2472_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2472_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
else
{
lean_dec(v_i_2463_);
lean_dec_ref(v_arg_2461_);
lean_dec_ref(v_fn_2460_);
lean_dec_ref_known(v_e_2442_, 2);
return v___x_2464_;
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref(v_e_2442_);
v___x_2518_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2, &l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
v___x_2519_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2518_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2519_;
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v_e_2442_);
v___x_2520_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_2455_);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_stop_2441_ = stack[0].m_obj;
lean_object* v_e_2442_ = stack[1].m_obj;
lean_object* v_i_2443_ = stack[2].m_obj;
lean_object* v_a_2444_ = stack[3].m_obj;
lean_object* v_a_2445_ = stack[4].m_obj;
lean_object* v_a_2446_ = stack[5].m_obj;
lean_object* v_a_2447_ = stack[6].m_obj;
lean_object* v_a_2448_ = stack[7].m_obj;
lean_object* v_a_2449_ = stack[8].m_obj;
lean_object* v_a_2450_ = stack[9].m_obj;
lean_object* v_a_2451_ = stack[10].m_obj;
lean_object* v_a_2452_ = stack[11].m_obj;
lean_object* v_res_2522_;
v_res_2522_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2441_, v_e_2442_, v_i_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
stack->m_obj
 = v_res_2522_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* v_stop_2523_, lean_object* v_e_2524_, lean_object* v_i_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2523_, v_e_2524_, v_i_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec(v_i_2525_);
lean_dec(v_stop_2523_);
return v_res_2536_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2539_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
v___x_2540_ = lean_unsigned_to_nat(2u);
v___x_2541_ = lean_unsigned_to_nat(488u);
v___x_2542_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
v___x_2544_ = l_mkPanicMessageWithDecl(v___x_2543_, v___x_2542_, v___x_2541_, v___x_2540_, v___x_2539_);
return v___x_2544_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* v_e_2545_, lean_object* v_start_2546_, lean_object* v_stop_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_nat_dec_lt(v_start_2546_, v_stop_2547_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec_ref(v_e_2545_);
v___x_2559_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2, &l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once, _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
v___x_2560_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_2559_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2560_;
}
else
{
lean_object* v_numArgs_2561_; uint8_t v___x_2562_; 
v_numArgs_2561_ = l_Lean_Expr_getAppNumArgs(v_e_2545_);
v___x_2562_ = lean_nat_dec_lt(v_numArgs_2561_, v_start_2546_);
if (v___x_2562_ == 0)
{
lean_object* v_numArgs_2563_; lean_object* v_stop_2564_; lean_object* v___x_2565_; 
v_numArgs_2563_ = lean_nat_sub(v_numArgs_2561_, v_start_2546_);
lean_dec(v_numArgs_2561_);
v_stop_2564_ = lean_nat_sub(v_stop_2547_, v_start_2546_);
v___x_2565_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_2564_, v_e_2545_, v_numArgs_2563_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_numArgs_2563_);
lean_dec(v_stop_2564_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_numArgs_2561_);
lean_dec_ref(v_e_2545_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8));
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpAppArgRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2545_ = stack[0].m_obj;
lean_object* v_start_2546_ = stack[1].m_obj;
lean_object* v_stop_2547_ = stack[2].m_obj;
lean_object* v_a_2548_ = stack[3].m_obj;
lean_object* v_a_2549_ = stack[4].m_obj;
lean_object* v_a_2550_ = stack[5].m_obj;
lean_object* v_a_2551_ = stack[6].m_obj;
lean_object* v_a_2552_ = stack[7].m_obj;
lean_object* v_a_2553_ = stack[8].m_obj;
lean_object* v_a_2554_ = stack[9].m_obj;
lean_object* v_a_2555_ = stack[10].m_obj;
lean_object* v_a_2556_ = stack[11].m_obj;
lean_object* v_res_2568_;
v_res_2568_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2545_, v_start_2546_, v_stop_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
stack->m_obj
 = v_res_2568_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* v_e_2569_, lean_object* v_start_2570_, lean_object* v_stop_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_2569_, v_start_2570_, v_stop_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec(v_stop_2571_);
lean_dec(v_start_2570_);
return v_res_2582_;
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
