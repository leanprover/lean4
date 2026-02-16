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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.Simp.App"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpOverApplied.visit"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.propagateOverApplied.visit"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "function type expected"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.getFnType"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpFixedPrefix.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpInterlaced.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpUsingCongrThm.simpEqArgs"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(uint8_t, lean_object*, size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpUsingCongrThm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4_value;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpAppArgRange.visit"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Sym.Simp.simpAppArgRange"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "assertion violation: start < stop\n  "};
static const lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_4);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
lean_inc(x_4);
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_app___override(x_1, x_2);
x_13 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_12, x_10);
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_12);
x_13 = l_Lean_Meta_Sym_getLevel___redArg(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l_Lean_Meta_Sym_inferType___redArg(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_16);
x_17 = l_Lean_Meta_Sym_getLevel___redArg(x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_3, x_22);
x_24 = l_Lean_mkAppB(x_23, x_12, x_16);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_mkConst(x_3, x_28);
x_30 = l_Lean_mkAppB(x_29, x_12, x_16);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
return x_15;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_16);
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_2, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
lean_inc_ref(x_3);
x_21 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_20, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_mkApp4(x_23, x_3, x_16, x_2, x_17);
x_25 = 0;
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_19);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_mkApp4(x_26, x_3, x_16, x_2, x_17);
x_28 = 0;
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_19);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_28);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_5);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_free_object(x_5);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_36);
lean_inc_ref(x_2);
x_38 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_2, x_36, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
lean_inc_ref(x_3);
x_41 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_40, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = l_Lean_mkApp4(x_42, x_3, x_36, x_2, x_37);
x_45 = 0;
x_46 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_52 = x_38;
} else {
 lean_dec_ref(x_38);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_54; 
lean_dec_ref(x_5);
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_55);
x_57 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_55, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
lean_inc_ref(x_3);
x_60 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_59, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l_Lean_mkApp4(x_62, x_2, x_55, x_56, x_3);
x_64 = 0;
lean_ctor_set(x_4, 1, x_63);
lean_ctor_set(x_4, 0, x_58);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_64);
lean_ctor_set(x_60, 0, x_4);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
x_66 = l_Lean_mkApp4(x_65, x_2, x_55, x_56, x_3);
x_67 = 0;
lean_ctor_set(x_4, 1, x_66);
lean_ctor_set(x_4, 0, x_58);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_4);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_58);
lean_free_object(x_4);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_69 = !lean_is_exclusive(x_60);
if (x_69 == 0)
{
return x_60;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
lean_dec(x_60);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_free_object(x_4);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_57);
if (x_72 == 0)
{
return x_57;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_57, 0);
lean_inc(x_73);
lean_dec(x_57);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_4, 0);
x_76 = lean_ctor_get(x_4, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_4);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_75);
x_77 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_75, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
lean_inc_ref(x_3);
x_80 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_79, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = l_Lean_mkApp4(x_81, x_2, x_75, x_76, x_3);
x_84 = 0;
x_85 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_84);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_91 = x_77;
} else {
 lean_dec_ref(x_77);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_94);
lean_dec_ref(x_4);
x_95 = !lean_is_exclusive(x_5);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_5, 0);
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_96);
lean_inc_ref(x_93);
x_98 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_93, x_96, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
lean_inc_ref(x_3);
x_101 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_100, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = l_Lean_mkApp6(x_103, x_2, x_93, x_3, x_96, x_94, x_97);
x_105 = 0;
lean_ctor_set(x_5, 1, x_104);
lean_ctor_set(x_5, 0, x_99);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_105);
lean_ctor_set(x_101, 0, x_5);
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec(x_101);
x_107 = l_Lean_mkApp6(x_106, x_2, x_93, x_3, x_96, x_94, x_97);
x_108 = 0;
lean_ctor_set(x_5, 1, x_107);
lean_ctor_set(x_5, 0, x_99);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_108);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_5);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_99);
lean_free_object(x_5);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
return x_101;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_101, 0);
lean_inc(x_111);
lean_dec(x_101);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_5);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_113 = !lean_is_exclusive(x_98);
if (x_113 == 0)
{
return x_98;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_98, 0);
lean_inc(x_114);
lean_dec(x_98);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_5, 0);
x_117 = lean_ctor_get(x_5, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_116);
lean_inc_ref(x_93);
x_118 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_93, x_116, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
lean_inc_ref(x_3);
x_121 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_120, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = l_Lean_mkApp6(x_122, x_2, x_93, x_3, x_116, x_94, x_117);
x_125 = 0;
x_126 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_125);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_119);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_128 = lean_ctor_get(x_121, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_131 = lean_ctor_get(x_118, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_132 = x_118;
} else {
 lean_dec_ref(x_118);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_mkCongr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_14 = l_Lean_Meta_Sym_inferType___redArg(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_16 = l_Lean_Meta_whnfD(x_15, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Sym_inferType___redArg(x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_21);
x_22 = l_Lean_Meta_Sym_getLevel___redArg(x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_24 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_26 = l_Lean_Meta_Sym_getLevel___redArg(x_25, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc_ref(x_3);
lean_inc_ref(x_4);
x_28 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_4, x_3, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = 0;
lean_inc(x_21);
x_32 = l_Lean_mkLambda(x_18, x_31, x_21, x_19);
x_33 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_mkConst(x_33, x_36);
x_38 = l_Lean_mkApp6(x_37, x_21, x_32, x_2, x_4, x_5, x_3);
x_39 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_6);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
x_41 = 0;
lean_inc(x_21);
x_42 = l_Lean_mkLambda(x_18, x_41, x_21, x_19);
x_43 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1));
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_mkConst(x_43, x_46);
x_48 = l_Lean_mkApp6(x_47, x_21, x_42, x_2, x_4, x_5, x_3);
x_49 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_6);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_28, 0);
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_24, 0);
lean_inc(x_58);
lean_dec(x_24);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_22);
if (x_60 == 0)
{
return x_22;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_22, 0);
lean_inc(x_61);
lean_dec(x_22);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_20, 0);
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_66 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
x_67 = l_Lean_indentExpr(x_2);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_68, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
return x_16;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_16, 0);
lean_inc(x_71);
lean_dec(x_16);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_14);
if (x_73 == 0)
{
return x_14;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_14, 0);
lean_inc(x_74);
lean_dec(x_14);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0;
x_13 = lean_panic_fn(x_12, x_1);
x_14 = lean_apply_10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(119u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(128u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_16);
x_20 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_1, x_16, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_16);
x_22 = l_Lean_Meta_Sym_inferType___redArg(x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_24 = l_Lean_Meta_whnfD(x_23, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 7)
{
lean_object* x_27; lean_object* x_28; uint8_t x_41; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_26);
x_41 = l_Lean_Expr_hasLooseBVars(x_28);
lean_dec_ref(x_28);
if (x_41 == 0)
{
lean_free_object(x_24);
goto block_40;
}
else
{
if (x_15 == 0)
{
lean_dec_ref(x_27);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_42; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_ctor_set_uint8(x_21, 0, x_15);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_43; 
lean_dec(x_21);
x_43 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_43, 0, x_15);
lean_ctor_set(x_24, 0, x_43);
return x_24;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_24);
x_44 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_21);
x_46 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_16, x_17, x_44, x_45, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_46;
}
}
else
{
lean_free_object(x_24);
goto block_40;
}
}
block_40:
{
lean_object* x_29; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_29 = l_Lean_Meta_isProp(x_27, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_32 = lean_sym_simp(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_16, x_17, x_21, x_33, x_7, x_8, x_9, x_10, x_11, x_12);
return x_34;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_35, 0, x_15);
x_36 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_16, x_17, x_21, x_35, x_7, x_8, x_9, x_10, x_11, x_12);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_2);
x_47 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
x_48 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_48;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_24, 0);
lean_inc(x_49);
lean_dec(x_24);
if (lean_obj_tag(x_49) == 7)
{
lean_object* x_50; lean_object* x_51; uint8_t x_64; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_49, 2);
lean_inc_ref(x_51);
lean_dec_ref(x_49);
x_64 = l_Lean_Expr_hasLooseBVars(x_51);
lean_dec_ref(x_51);
if (x_64 == 0)
{
goto block_63;
}
else
{
if (x_15 == 0)
{
lean_dec_ref(x_50);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_21)) {
 x_65 = x_21;
} else {
 lean_dec_ref(x_21);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 0, 1);
} else {
 x_66 = x_65;
}
lean_ctor_set_uint8(x_66, 0, x_15);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_69);
lean_dec_ref(x_21);
x_70 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_16, x_17, x_68, x_69, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_70;
}
}
else
{
goto block_63;
}
}
block_63:
{
lean_object* x_52; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_52 = l_Lean_Meta_isProp(x_50, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_55 = lean_sym_simp(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_16, x_17, x_21, x_56, x_7, x_8, x_9, x_10, x_11, x_12);
return x_57;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_55;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_58, 0, x_15);
x_59 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_16, x_17, x_21, x_58, x_7, x_8, x_9, x_10, x_11, x_12);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_61 = x_52;
} else {
 lean_dec_ref(x_52);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_49);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_2);
x_71 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
x_72 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_71, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_73 = !lean_is_exclusive(x_24);
if (x_73 == 0)
{
return x_24;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_24, 0);
lean_inc(x_74);
lean_dec(x_24);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_76 = !lean_is_exclusive(x_22);
if (x_76 == 0)
{
return x_22;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_22, 0);
lean_inc(x_77);
lean_dec(x_22);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_79 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4;
x_80 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_80;
}
}
else
{
lean_object* x_81; 
x_81 = lean_apply_11(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_81;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_simpOverApplied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(165u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_16);
x_20 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(x_1, x_16, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
lean_dec_ref(x_21);
x_25 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_16, x_17, x_22, x_23, x_24, x_7, x_8, x_9, x_10, x_11, x_12);
return x_25;
}
}
else
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1;
x_27 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_apply_11(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isForall(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Lean_Meta_whnfD(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_isForall(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1;
x_13 = l_Lean_MessageData_ofExpr(x_10);
x_14 = l_Lean_indentD(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_15, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_10, x_2);
return x_20;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
else
{
lean_object* x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0;
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2));
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3));
x_39 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4));
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_Lean_instInhabitedExpr;
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_7(x_50, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 2);
x_54 = lean_ctor_get(x_30, 3);
x_55 = lean_ctor_get(x_30, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_56 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3));
x_57 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4));
lean_inc_ref(x_52);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_53);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_28, 1, x_57);
lean_ctor_set(x_28, 0, x_64);
x_65 = l_ReaderT_instMonad___redArg(x_28);
x_66 = l_Lean_instInhabitedExpr;
x_67 = l_instInhabitedOfMonad___redArg(x_65, x_66);
x_68 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_68, 0, x_67);
x_69 = lean_panic_fn(x_68, x_1);
x_70 = lean_apply_7(x_69, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
lean_dec(x_28);
x_72 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 4);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3));
x_78 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4));
lean_inc_ref(x_72);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_74);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_73);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
x_87 = l_ReaderT_instMonad___redArg(x_86);
x_88 = l_Lean_instInhabitedExpr;
x_89 = l_instInhabitedOfMonad___redArg(x_87, x_88);
x_90 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_panic_fn(x_90, x_1);
x_92 = lean_apply_7(x_91, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 2);
x_95 = lean_ctor_get(x_12, 3);
x_96 = lean_ctor_get(x_12, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_97 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1));
x_98 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2));
lean_inc_ref(x_93);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_99, 0, x_93);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_102, 0, x_96);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_103, 0, x_95);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_104, 0, x_94);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_10, 1, x_98);
lean_ctor_set(x_10, 0, x_105);
x_106 = l_ReaderT_instMonad___redArg(x_10);
x_107 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_107, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3));
x_115 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4));
lean_inc_ref(x_109);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_120, 0, x_111);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_121, 0, x_110);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_119);
if (lean_is_scalar(x_108)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_108;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_ReaderT_instMonad___redArg(x_123);
x_125 = l_Lean_instInhabitedExpr;
x_126 = l_instInhabitedOfMonad___redArg(x_124, x_125);
x_127 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_127, 0, x_126);
x_128 = lean_panic_fn(x_127, x_1);
x_129 = lean_apply_7(x_128, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_130 = lean_ctor_get(x_10, 0);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_130, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 4);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1));
x_137 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2));
lean_inc_ref(x_131);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_138, 0, x_131);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_139, 0, x_131);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_141, 0, x_134);
x_142 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_142, 0, x_133);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_143, 0, x_132);
if (lean_is_scalar(x_135)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_135;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_141);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
x_146 = l_ReaderT_instMonad___redArg(x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_147, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 4);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
x_154 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3));
x_155 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4));
lean_inc_ref(x_149);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_156, 0, x_149);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_157, 0, x_149);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_159, 0, x_152);
x_160 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_160, 0, x_151);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_161, 0, x_150);
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_153;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_160);
lean_ctor_set(x_162, 4, x_159);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_148;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_155);
x_164 = l_ReaderT_instMonad___redArg(x_163);
x_165 = l_Lean_instInhabitedExpr;
x_166 = l_instInhabitedOfMonad___redArg(x_164, x_165);
x_167 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_167, 0, x_166);
x_168 = lean_panic_fn(x_167, x_1);
x_169 = lean_apply_7(x_168, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_169;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(196u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 1)
{
lean_object* x_12; 
lean_dec_ref(x_3);
x_12 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
x_15 = l_Lean_Expr_appFn_x21(x_1);
lean_dec_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_16 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_15, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_17, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_18);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
x_23 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(x_22, x_3, x_4, x_5, x_6, x_7, x_8);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 7)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
x_28 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(x_27, x_3, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_4);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
lean_inc(x_4);
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_app___override(x_1, x_2);
x_13 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_12, x_10);
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0;
x_13 = lean_panic_fn(x_12, x_1);
x_14 = lean_apply_10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(256u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(248u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(263u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_unsigned_to_nat(243u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_1, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_15);
x_19 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(x_18, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_16);
x_24 = lean_sym_simp(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_25; 
lean_dec(x_23);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_ctor_set_uint8(x_26, 0, x_14);
x_28 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_20, 0, x_26);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_29, 0, x_14);
x_30 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
lean_ctor_set(x_20, 1, x_30);
lean_ctor_set(x_20, 0, x_29);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_24);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_15);
x_34 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_15, x_18, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_36 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 7)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_37, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_37);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_32);
lean_inc_ref(x_15);
x_40 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_15, x_32, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_38);
x_42 = l_Lean_Meta_Sym_getLevel___redArg(x_38, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc_ref(x_39);
x_44 = l_Lean_Meta_Sym_getLevel___redArg(x_39, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_mkConst(x_47, x_50);
lean_inc_ref(x_39);
x_52 = l_Lean_mkApp6(x_51, x_38, x_39, x_16, x_32, x_15, x_33);
lean_ctor_set(x_26, 1, x_52);
lean_ctor_set(x_26, 0, x_41);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_39);
lean_ctor_set(x_20, 0, x_26);
lean_ctor_set(x_44, 0, x_20);
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_mkConst(x_54, x_57);
lean_inc_ref(x_39);
x_59 = l_Lean_mkApp6(x_58, x_38, x_39, x_16, x_32, x_15, x_33);
lean_ctor_set(x_26, 1, x_59);
lean_ctor_set(x_26, 0, x_41);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_39);
lean_ctor_set(x_20, 0, x_26);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_20);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_free_object(x_26);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_61 = !lean_is_exclusive(x_44);
if (x_61 == 0)
{
return x_44;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
lean_dec(x_44);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_free_object(x_26);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
return x_42;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
lean_dec(x_42);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_free_object(x_26);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_67 = !lean_is_exclusive(x_40);
if (x_67 == 0)
{
return x_40;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_40, 0);
lean_inc(x_68);
lean_dec(x_40);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_37);
lean_free_object(x_26);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_70 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_71 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_free_object(x_26);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_36);
if (x_72 == 0)
{
return x_36;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_36, 0);
lean_inc(x_73);
lean_dec(x_36);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_free_object(x_26);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_34);
if (x_75 == 0)
{
return x_34;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_34, 0);
lean_inc(x_76);
lean_dec(x_34);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_26, 0);
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_26);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_15);
x_80 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_15, x_18, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_82 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_81, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
if (lean_obj_tag(x_83) == 7)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_84 = lean_ctor_get(x_83, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_83, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_83);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_78);
lean_inc_ref(x_15);
x_86 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_15, x_78, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_84);
x_88 = l_Lean_Meta_Sym_getLevel___redArg(x_84, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
lean_inc_ref(x_85);
x_90 = l_Lean_Meta_Sym_getLevel___redArg(x_85, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_mkConst(x_93, x_96);
lean_inc_ref(x_85);
x_98 = l_Lean_mkApp6(x_97, x_84, x_85, x_16, x_78, x_15, x_79);
x_99 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_99, 0, x_87);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_85);
lean_ctor_set(x_20, 0, x_99);
if (lean_is_scalar(x_92)) {
 x_100 = lean_alloc_ctor(0, 1, 0);
} else {
 x_100 = x_92;
}
lean_ctor_set(x_100, 0, x_20);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_101 = lean_ctor_get(x_90, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_102 = x_90;
} else {
 lean_dec_ref(x_90);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_87);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_104 = lean_ctor_get(x_88, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_105 = x_88;
} else {
 lean_dec_ref(x_88);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_107 = lean_ctor_get(x_86, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_108 = x_86;
} else {
 lean_dec_ref(x_86);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_83);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_110 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_111 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_110, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_82, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_113 = x_82;
} else {
 lean_dec_ref(x_82);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_115 = lean_ctor_get(x_80, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_116 = x_80;
} else {
 lean_dec_ref(x_80);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_24, 0);
lean_inc(x_118);
lean_dec(x_24);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_is_exclusive(x_118)) {
 x_119 = x_118;
} else {
 lean_dec_ref(x_118);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 0, 1);
} else {
 x_120 = x_119;
}
lean_ctor_set_uint8(x_120, 0, x_14);
x_121 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
lean_ctor_set(x_20, 1, x_121);
lean_ctor_set(x_20, 0, x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_20);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_118, 1);
lean_inc_ref(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_15);
x_126 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_15, x_18, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_128 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_127, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
if (lean_obj_tag(x_129) == 7)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_130 = lean_ctor_get(x_129, 1);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_129, 2);
lean_inc_ref(x_131);
lean_dec_ref(x_129);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_123);
lean_inc_ref(x_15);
x_132 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_15, x_123, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_130);
x_134 = l_Lean_Meta_Sym_getLevel___redArg(x_130, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
lean_inc_ref(x_131);
x_136 = l_Lean_Meta_Sym_getLevel___redArg(x_131, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_135);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_mkConst(x_139, x_142);
lean_inc_ref(x_131);
x_144 = l_Lean_mkApp6(x_143, x_130, x_131, x_16, x_123, x_15, x_124);
if (lean_is_scalar(x_125)) {
 x_145 = lean_alloc_ctor(1, 2, 1);
} else {
 x_145 = x_125;
}
lean_ctor_set(x_145, 0, x_133);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_131);
lean_ctor_set(x_20, 0, x_145);
if (lean_is_scalar(x_138)) {
 x_146 = lean_alloc_ctor(0, 1, 0);
} else {
 x_146 = x_138;
}
lean_ctor_set(x_146, 0, x_20);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_147 = lean_ctor_get(x_136, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_148 = x_136;
} else {
 lean_dec_ref(x_136);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_133);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_150 = lean_ctor_get(x_134, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_129);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_156 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_157 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_158 = lean_ctor_get(x_128, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_159 = x_128;
} else {
 lean_dec_ref(x_128);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_161 = lean_ctor_get(x_126, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_162 = x_126;
} else {
 lean_dec_ref(x_126);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_18);
x_164 = lean_ctor_get(x_24, 0);
lean_inc(x_164);
lean_dec_ref(x_24);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
lean_dec_ref(x_164);
x_165 = !lean_is_exclusive(x_22);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_22, 0);
x_167 = lean_ctor_get(x_22, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_168 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
if (lean_obj_tag(x_169) == 7)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_170 = lean_ctor_get(x_169, 1);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_169, 2);
lean_inc_ref(x_171);
lean_dec_ref(x_169);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
lean_inc_ref(x_166);
x_172 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_166, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_170);
x_174 = l_Lean_Meta_Sym_getLevel___redArg(x_170, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
lean_inc_ref(x_171);
x_176 = l_Lean_Meta_Sym_getLevel___redArg(x_171, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_mkConst(x_179, x_182);
lean_inc_ref(x_171);
x_184 = l_Lean_mkApp6(x_183, x_170, x_171, x_15, x_166, x_167, x_16);
lean_ctor_set(x_22, 1, x_184);
lean_ctor_set(x_22, 0, x_173);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_171);
lean_ctor_set(x_176, 0, x_20);
return x_176;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_185 = lean_ctor_get(x_176, 0);
lean_inc(x_185);
lean_dec(x_176);
x_186 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_175);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_mkConst(x_186, x_189);
lean_inc_ref(x_171);
x_191 = l_Lean_mkApp6(x_190, x_170, x_171, x_15, x_166, x_167, x_16);
lean_ctor_set(x_22, 1, x_191);
lean_ctor_set(x_22, 0, x_173);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_171);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_20);
return x_192;
}
}
else
{
uint8_t x_193; 
lean_dec(x_175);
lean_dec(x_173);
lean_dec_ref(x_171);
lean_dec_ref(x_170);
lean_free_object(x_22);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_193 = !lean_is_exclusive(x_176);
if (x_193 == 0)
{
return x_176;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_176, 0);
lean_inc(x_194);
lean_dec(x_176);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_173);
lean_dec_ref(x_171);
lean_dec_ref(x_170);
lean_free_object(x_22);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_196 = !lean_is_exclusive(x_174);
if (x_196 == 0)
{
return x_174;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_174, 0);
lean_inc(x_197);
lean_dec(x_174);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec_ref(x_171);
lean_dec_ref(x_170);
lean_free_object(x_22);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_199 = !lean_is_exclusive(x_172);
if (x_199 == 0)
{
return x_172;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_172, 0);
lean_inc(x_200);
lean_dec(x_172);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_169);
lean_free_object(x_22);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_202 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
x_203 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_202, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_203;
}
}
else
{
uint8_t x_204; 
lean_free_object(x_22);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_204 = !lean_is_exclusive(x_168);
if (x_204 == 0)
{
return x_168;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_168, 0);
lean_inc(x_205);
lean_dec(x_168);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_22, 0);
x_208 = lean_ctor_get(x_22, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_209 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
if (lean_obj_tag(x_210) == 7)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_211 = lean_ctor_get(x_210, 1);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_210, 2);
lean_inc_ref(x_212);
lean_dec_ref(x_210);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
lean_inc_ref(x_207);
x_213 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_207, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_211);
x_215 = l_Lean_Meta_Sym_getLevel___redArg(x_211, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
lean_inc_ref(x_212);
x_217 = l_Lean_Meta_Sym_getLevel___redArg(x_212, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_216);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_mkConst(x_220, x_223);
lean_inc_ref(x_212);
x_225 = l_Lean_mkApp6(x_224, x_211, x_212, x_15, x_207, x_208, x_16);
x_226 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_226, 0, x_214);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_212);
lean_ctor_set(x_20, 0, x_226);
if (lean_is_scalar(x_219)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_219;
}
lean_ctor_set(x_227, 0, x_20);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_216);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_228 = lean_ctor_get(x_217, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_229 = x_217;
} else {
 lean_dec_ref(x_217);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_231 = lean_ctor_get(x_215, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_232 = x_215;
} else {
 lean_dec_ref(x_215);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_234 = lean_ctor_get(x_213, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_235 = x_213;
} else {
 lean_dec_ref(x_213);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_210);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_237 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
x_238 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_237, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_239 = lean_ctor_get(x_209, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_240 = x_209;
} else {
 lean_dec_ref(x_209);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_243);
lean_dec_ref(x_22);
x_244 = !lean_is_exclusive(x_164);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_164, 0);
x_246 = lean_ctor_get(x_164, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_247 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
if (lean_obj_tag(x_248) == 7)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_249 = lean_ctor_get(x_248, 1);
lean_inc_ref(x_249);
x_250 = lean_ctor_get(x_248, 2);
lean_inc_ref(x_250);
lean_dec_ref(x_248);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_245);
lean_inc_ref(x_242);
x_251 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_242, x_245, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_249);
x_253 = l_Lean_Meta_Sym_getLevel___redArg(x_249, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
lean_inc_ref(x_250);
x_255 = l_Lean_Meta_Sym_getLevel___redArg(x_250, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_254);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_mkConst(x_258, x_261);
lean_inc_ref(x_250);
x_263 = l_Lean_mkApp8(x_262, x_249, x_250, x_15, x_242, x_16, x_245, x_243, x_246);
lean_ctor_set(x_164, 1, x_263);
lean_ctor_set(x_164, 0, x_252);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_250);
lean_ctor_set(x_20, 0, x_164);
lean_ctor_set(x_255, 0, x_20);
return x_255;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_264 = lean_ctor_get(x_255, 0);
lean_inc(x_264);
lean_dec(x_255);
x_265 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
x_266 = lean_box(0);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_254);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_mkConst(x_265, x_268);
lean_inc_ref(x_250);
x_270 = l_Lean_mkApp8(x_269, x_249, x_250, x_15, x_242, x_16, x_245, x_243, x_246);
lean_ctor_set(x_164, 1, x_270);
lean_ctor_set(x_164, 0, x_252);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_250);
lean_ctor_set(x_20, 0, x_164);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_20);
return x_271;
}
}
else
{
uint8_t x_272; 
lean_dec(x_254);
lean_dec(x_252);
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_free_object(x_164);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_272 = !lean_is_exclusive(x_255);
if (x_272 == 0)
{
return x_255;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_255, 0);
lean_inc(x_273);
lean_dec(x_255);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_252);
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_free_object(x_164);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_275 = !lean_is_exclusive(x_253);
if (x_275 == 0)
{
return x_253;
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_253, 0);
lean_inc(x_276);
lean_dec(x_253);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
uint8_t x_278; 
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_free_object(x_164);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_278 = !lean_is_exclusive(x_251);
if (x_278 == 0)
{
return x_251;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_251, 0);
lean_inc(x_279);
lean_dec(x_251);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_248);
lean_free_object(x_164);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_281 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
x_282 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_281, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_282;
}
}
else
{
uint8_t x_283; 
lean_free_object(x_164);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_283 = !lean_is_exclusive(x_247);
if (x_283 == 0)
{
return x_247;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_247, 0);
lean_inc(x_284);
lean_dec(x_247);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_164, 0);
x_287 = lean_ctor_get(x_164, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_164);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_288 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
if (lean_obj_tag(x_289) == 7)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_290 = lean_ctor_get(x_289, 1);
lean_inc_ref(x_290);
x_291 = lean_ctor_get(x_289, 2);
lean_inc_ref(x_291);
lean_dec_ref(x_289);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_286);
lean_inc_ref(x_242);
x_292 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_242, x_286, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_290);
x_294 = l_Lean_Meta_Sym_getLevel___redArg(x_290, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
lean_inc_ref(x_291);
x_296 = l_Lean_Meta_Sym_getLevel___redArg(x_291, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
x_299 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
x_300 = lean_box(0);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_295);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_mkConst(x_299, x_302);
lean_inc_ref(x_291);
x_304 = l_Lean_mkApp8(x_303, x_290, x_291, x_15, x_242, x_16, x_286, x_243, x_287);
x_305 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_305, 0, x_293);
lean_ctor_set(x_305, 1, x_304);
lean_ctor_set_uint8(x_305, sizeof(void*)*2, x_14);
lean_ctor_set(x_20, 1, x_291);
lean_ctor_set(x_20, 0, x_305);
if (lean_is_scalar(x_298)) {
 x_306 = lean_alloc_ctor(0, 1, 0);
} else {
 x_306 = x_298;
}
lean_ctor_set(x_306, 0, x_20);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_295);
lean_dec(x_293);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_307 = lean_ctor_get(x_296, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_308 = x_296;
} else {
 lean_dec_ref(x_296);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 1, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_293);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_310 = lean_ctor_get(x_294, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_311 = x_294;
} else {
 lean_dec_ref(x_294);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 1, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_313 = lean_ctor_get(x_292, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_314 = x_292;
} else {
 lean_dec_ref(x_292);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_289);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_316 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
x_317 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_316, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_free_object(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_318 = lean_ctor_get(x_288, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_319 = x_288;
} else {
 lean_dec_ref(x_288);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
return x_320;
}
}
}
}
}
else
{
uint8_t x_321; 
lean_free_object(x_20);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_321 = !lean_is_exclusive(x_24);
if (x_321 == 0)
{
return x_24;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_24, 0);
lean_inc(x_322);
lean_dec(x_24);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_20, 0);
x_325 = lean_ctor_get(x_20, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_20);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_16);
x_326 = lean_sym_simp(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_325);
lean_dec_ref(x_324);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_328 = x_326;
} else {
 lean_dec_ref(x_326);
 x_328 = lean_box(0);
}
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_is_exclusive(x_327)) {
 x_329 = x_327;
} else {
 lean_dec_ref(x_327);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 0, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set_uint8(x_330, 0, x_14);
x_331 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
if (lean_is_scalar(x_328)) {
 x_333 = lean_alloc_ctor(0, 1, 0);
} else {
 x_333 = x_328;
}
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_328);
x_334 = lean_ctor_get(x_327, 0);
lean_inc_ref(x_334);
x_335 = lean_ctor_get(x_327, 1);
lean_inc_ref(x_335);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_336 = x_327;
} else {
 lean_dec_ref(x_327);
 x_336 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_15);
x_337 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_15, x_18, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
lean_dec_ref(x_337);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_339 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_338, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
if (lean_obj_tag(x_340) == 7)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_341 = lean_ctor_get(x_340, 1);
lean_inc_ref(x_341);
x_342 = lean_ctor_get(x_340, 2);
lean_inc_ref(x_342);
lean_dec_ref(x_340);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_334);
lean_inc_ref(x_15);
x_343 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_15, x_334, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_341);
x_345 = l_Lean_Meta_Sym_getLevel___redArg(x_341, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
lean_dec_ref(x_345);
lean_inc_ref(x_342);
x_347 = l_Lean_Meta_Sym_getLevel___redArg(x_342, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_349 = x_347;
} else {
 lean_dec_ref(x_347);
 x_349 = lean_box(0);
}
x_350 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2));
x_351 = lean_box(0);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_348);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_346);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_mkConst(x_350, x_353);
lean_inc_ref(x_342);
x_355 = l_Lean_mkApp6(x_354, x_341, x_342, x_16, x_334, x_15, x_335);
if (lean_is_scalar(x_336)) {
 x_356 = lean_alloc_ctor(1, 2, 1);
} else {
 x_356 = x_336;
}
lean_ctor_set(x_356, 0, x_344);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set_uint8(x_356, sizeof(void*)*2, x_14);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_342);
if (lean_is_scalar(x_349)) {
 x_358 = lean_alloc_ctor(0, 1, 0);
} else {
 x_358 = x_349;
}
lean_ctor_set(x_358, 0, x_357);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_346);
lean_dec(x_344);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_359 = lean_ctor_get(x_347, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_344);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_362 = lean_ctor_get(x_345, 0);
lean_inc(x_362);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 x_363 = x_345;
} else {
 lean_dec_ref(x_345);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_365 = lean_ctor_get(x_343, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_366 = x_343;
} else {
 lean_dec_ref(x_343);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; 
lean_dec(x_340);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_368 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_369 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_368, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_370 = lean_ctor_get(x_339, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 x_371 = x_339;
} else {
 lean_dec_ref(x_339);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 1, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_373 = lean_ctor_get(x_337, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_374 = x_337;
} else {
 lean_dec_ref(x_337);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 1, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_373);
return x_375;
}
}
}
else
{
lean_object* x_376; 
lean_dec(x_18);
x_376 = lean_ctor_get(x_326, 0);
lean_inc(x_376);
lean_dec_ref(x_326);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec_ref(x_376);
x_377 = lean_ctor_get(x_324, 0);
lean_inc_ref(x_377);
x_378 = lean_ctor_get(x_324, 1);
lean_inc_ref(x_378);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_379 = x_324;
} else {
 lean_dec_ref(x_324);
 x_379 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_380 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_325, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec_ref(x_380);
if (lean_obj_tag(x_381) == 7)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_382 = lean_ctor_get(x_381, 1);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_381, 2);
lean_inc_ref(x_383);
lean_dec_ref(x_381);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
lean_inc_ref(x_377);
x_384 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_377, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec_ref(x_384);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_382);
x_386 = l_Lean_Meta_Sym_getLevel___redArg(x_382, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec_ref(x_386);
lean_inc_ref(x_383);
x_388 = l_Lean_Meta_Sym_getLevel___redArg(x_383, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_390 = x_388;
} else {
 lean_dec_ref(x_388);
 x_390 = lean_box(0);
}
x_391 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4));
x_392 = lean_box(0);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_389);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_387);
lean_ctor_set(x_394, 1, x_393);
x_395 = l_Lean_mkConst(x_391, x_394);
lean_inc_ref(x_383);
x_396 = l_Lean_mkApp6(x_395, x_382, x_383, x_15, x_377, x_378, x_16);
if (lean_is_scalar(x_379)) {
 x_397 = lean_alloc_ctor(1, 2, 1);
} else {
 x_397 = x_379;
}
lean_ctor_set(x_397, 0, x_385);
lean_ctor_set(x_397, 1, x_396);
lean_ctor_set_uint8(x_397, sizeof(void*)*2, x_14);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_383);
if (lean_is_scalar(x_390)) {
 x_399 = lean_alloc_ctor(0, 1, 0);
} else {
 x_399 = x_390;
}
lean_ctor_set(x_399, 0, x_398);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_387);
lean_dec(x_385);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_400 = lean_ctor_get(x_388, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_401 = x_388;
} else {
 lean_dec_ref(x_388);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 1, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_385);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_403 = lean_ctor_get(x_386, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 x_404 = x_386;
} else {
 lean_dec_ref(x_386);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 1, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_403);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_406 = lean_ctor_get(x_384, 0);
lean_inc(x_406);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 x_407 = x_384;
} else {
 lean_dec_ref(x_384);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_406);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_409 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
x_410 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_409, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_411 = lean_ctor_get(x_380, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 x_412 = x_380;
} else {
 lean_dec_ref(x_380);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 1, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_414 = lean_ctor_get(x_324, 0);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_324, 1);
lean_inc_ref(x_415);
lean_dec_ref(x_324);
x_416 = lean_ctor_get(x_376, 0);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_376, 1);
lean_inc_ref(x_417);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_418 = x_376;
} else {
 lean_dec_ref(x_376);
 x_418 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_419 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(x_325, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
if (lean_obj_tag(x_420) == 7)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_421 = lean_ctor_get(x_420, 1);
lean_inc_ref(x_421);
x_422 = lean_ctor_get(x_420, 2);
lean_inc_ref(x_422);
lean_dec_ref(x_420);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_416);
lean_inc_ref(x_414);
x_423 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_414, x_416, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
lean_dec_ref(x_423);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_421);
x_425 = l_Lean_Meta_Sym_getLevel___redArg(x_421, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec_ref(x_425);
lean_inc_ref(x_422);
x_427 = l_Lean_Meta_Sym_getLevel___redArg(x_422, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6));
x_431 = lean_box(0);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_431);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_426);
lean_ctor_set(x_433, 1, x_432);
x_434 = l_Lean_mkConst(x_430, x_433);
lean_inc_ref(x_422);
x_435 = l_Lean_mkApp8(x_434, x_421, x_422, x_15, x_414, x_16, x_416, x_415, x_417);
if (lean_is_scalar(x_418)) {
 x_436 = lean_alloc_ctor(1, 2, 1);
} else {
 x_436 = x_418;
}
lean_ctor_set(x_436, 0, x_424);
lean_ctor_set(x_436, 1, x_435);
lean_ctor_set_uint8(x_436, sizeof(void*)*2, x_14);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_422);
if (lean_is_scalar(x_429)) {
 x_438 = lean_alloc_ctor(0, 1, 0);
} else {
 x_438 = x_429;
}
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_426);
lean_dec(x_424);
lean_dec_ref(x_422);
lean_dec_ref(x_421);
lean_dec(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_439 = lean_ctor_get(x_427, 0);
lean_inc(x_439);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_440 = x_427;
} else {
 lean_dec_ref(x_427);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_424);
lean_dec_ref(x_422);
lean_dec_ref(x_421);
lean_dec(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_442 = lean_ctor_get(x_425, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_443 = x_425;
} else {
 lean_dec_ref(x_425);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec_ref(x_422);
lean_dec_ref(x_421);
lean_dec(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_445 = lean_ctor_get(x_423, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_446 = x_423;
} else {
 lean_dec_ref(x_423);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; 
lean_dec(x_420);
lean_dec(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_448 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
x_449 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_448, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_450 = lean_ctor_get(x_419, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_451 = x_419;
} else {
 lean_dec_ref(x_419);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 1, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_450);
return x_452;
}
}
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_453 = lean_ctor_get(x_326, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_454 = x_326;
} else {
 lean_dec_ref(x_326);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_453);
return x_455;
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_19;
}
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec_ref(x_2);
x_456 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7;
x_457 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_456, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_458 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
x_459 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_459, 0, x_458);
return x_459;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
x_15 = lean_nat_dec_le(x_14, x_2);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_add(x_2, x_3);
x_17 = lean_nat_dec_lt(x_16, x_14);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_nat_sub(x_14, x_2);
lean_dec(x_14);
x_19 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(x_18, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_nat_sub(x_14, x_2);
lean_dec(x_14);
x_21 = lean_nat_sub(x_20, x_3);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 12, 1);
lean_closure_set(x_22, 0, x_3);
x_23 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_22, x_1, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_24 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_simpFixedPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(298u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_2, x_18);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_16);
x_20 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_array_fget_borrowed(x_1, x_19);
lean_dec(x_19);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_25; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_22, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 0, 1);
x_28 = lean_unbox(x_23);
lean_ctor_set_uint8(x_27, 0, x_28);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_free_object(x_20);
x_29 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_22);
x_31 = lean_unbox(x_23);
x_32 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_3, x_16, x_17, x_29, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_12);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_free_object(x_20);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_33 = lean_sym_simp(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_16, x_17, x_22, x_34, x_7, x_8, x_9, x_10, x_11, x_12);
return x_35;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_33;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_array_fget_borrowed(x_1, x_19);
lean_dec(x_19);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
if (lean_is_exclusive(x_36)) {
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 0, 1);
} else {
 x_40 = x_39;
}
x_41 = lean_unbox(x_37);
lean_ctor_set_uint8(x_40, 0, x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_36);
x_45 = lean_unbox(x_37);
x_46 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_3, x_16, x_17, x_43, x_44, x_45, x_7, x_8, x_9, x_10, x_11, x_12);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_47 = lean_sym_simp(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_16, x_17, x_36, x_48, x_7, x_8, x_9, x_10, x_11, x_12);
return x_49;
}
else
{
lean_dec(x_36);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_47;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_20;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_3);
x_50 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1;
x_51 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_52 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_2);
x_17 = lean_nat_dec_lt(x_16, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_2, x_13, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
lean_dec_ref(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 13, 2);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_16);
x_20 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_21 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_19, x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
lean_object* x_7; 
x_7 = lean_array_push(x_1, x_3);
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_array_push(x_1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_1);
x_11 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_12 = lean_mk_array(x_2, x_11);
x_13 = lean_array_push(x_12, x_3);
return x_13;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(411u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_3);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_array_get_borrowed(x_34, x_1, x_4);
x_36 = lean_unbox(x_35);
switch (x_36) {
case 5:
{
lean_dec_ref(x_18);
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = x_14;
x_27 = x_15;
x_28 = lean_box(0);
goto block_32;
}
case 0:
{
lean_dec_ref(x_18);
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = x_14;
x_27 = x_15;
x_28 = lean_box(0);
goto block_32;
}
case 3:
{
lean_dec_ref(x_18);
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = x_14;
x_27 = x_15;
x_28 = lean_box(0);
goto block_32;
}
case 2:
{
lean_object* x_37; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_37 = lean_sym_simp(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_4, x_39);
lean_dec(x_4);
x_41 = lean_nat_add(x_5, x_39);
x_42 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(x_6, x_5, x_38);
x_3 = x_17;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_37;
}
}
default: 
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_44 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1;
x_45 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_45;
}
}
block_32:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_4, x_29);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_30;
x_7 = x_19;
x_8 = x_20;
x_9 = x_21;
x_10 = x_22;
x_11 = x_23;
x_12 = x_24;
x_13 = x_25;
x_14 = x_26;
x_15 = x_27;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_46 = l_Array_isEmpty___redArg(x_6);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Array_reverse___redArg(x_6);
x_48 = lean_apply_11(x_2, x_47, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, lean_box(0));
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_49 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_1);
return x_17;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0;
x_13 = lean_panic_fn(x_12, x_1);
x_14 = lean_apply_10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; lean_object* x_12; uint8_t x_13; 
x_6 = 1;
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 3)
{
x_7 = x_1;
goto block_11;
}
else
{
x_7 = x_5;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(391u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_4, x_3);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_25 = x_5;
} else {
 lean_dec_ref(x_5);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_32 = x_26;
} else {
 lean_dec_ref(x_26);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_37 = x_28;
} else {
 lean_dec_ref(x_28);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
x_41 = lean_box(0);
x_42 = lean_nat_dec_lt(x_39, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_36);
if (lean_is_scalar(x_34)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_34;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_32)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_32;
}
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_30)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_30;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_25)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_25;
}
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_inc(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_95; 
x_50 = lean_ctor_get(x_29, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_29, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_29, 0);
lean_dec(x_52);
x_53 = lean_array_uget(x_2, x_4);
x_54 = lean_array_fget(x_38, x_39);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_39, x_55);
lean_dec(x_39);
lean_ctor_set(x_29, 1, x_56);
lean_inc(x_53);
x_85 = l_Lean_Expr_app___override(x_33, x_53);
x_86 = l_Lean_Expr_bindingBody_x21(x_36);
lean_dec(x_36);
x_95 = lean_unbox(x_54);
lean_dec(x_54);
switch (x_95) {
case 0:
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_87 = lean_box(0);
goto block_94;
}
case 3:
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_87 = lean_box(0);
goto block_94;
}
case 5:
{
lean_object* x_96; lean_object* x_97; 
lean_inc(x_53);
x_96 = lean_array_push(x_35, x_53);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_53);
x_97 = l_Lean_Meta_Sym_inferType___redArg(x_53, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Expr_bindingDomain_x21(x_86);
x_100 = lean_expr_instantiate_rev(x_99, x_96);
lean_dec_ref(x_99);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_100);
x_101 = l_Lean_Meta_Sym_isDefEqI___redArg(x_98, x_100, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_53);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_104 = l_Lean_Meta_trySynthInstance(x_100, x_41, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 0);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; 
lean_free_object(x_104);
lean_dec(x_102);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_57 = x_85;
x_58 = x_96;
x_59 = x_86;
x_60 = x_107;
x_61 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_106);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_108 = lean_alloc_ctor(0, 0, 1);
x_109 = lean_unbox(x_102);
lean_dec(x_102);
lean_ctor_set_uint8(x_108, 0, x_109);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_96);
lean_ctor_set(x_111, 1, x_86);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_85);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_31);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_29);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_104, 0, x_115);
return x_104;
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_104, 0);
lean_inc(x_116);
lean_dec(x_104);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; 
lean_dec(x_102);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_57 = x_85;
x_58 = x_96;
x_59 = x_86;
x_60 = x_117;
x_61 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_116);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_118 = lean_alloc_ctor(0, 0, 1);
x_119 = lean_unbox(x_102);
lean_dec(x_102);
lean_ctor_set_uint8(x_118, 0, x_119);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_96);
lean_ctor_set(x_121, 1, x_86);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_85);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_31);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_29);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_102);
lean_dec_ref(x_96);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_29);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_127 = !lean_is_exclusive(x_104);
if (x_127 == 0)
{
return x_104;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_104, 0);
lean_inc(x_128);
lean_dec(x_104);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
lean_dec(x_102);
lean_dec_ref(x_100);
x_57 = x_85;
x_58 = x_96;
x_59 = x_86;
x_60 = x_53;
x_61 = lean_box(0);
goto block_70;
}
}
else
{
uint8_t x_130; 
lean_dec_ref(x_100);
lean_dec_ref(x_96);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_29);
lean_dec(x_53);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_130 = !lean_is_exclusive(x_101);
if (x_130 == 0)
{
return x_101;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_101, 0);
lean_inc(x_131);
lean_dec(x_101);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec_ref(x_96);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_29);
lean_dec(x_53);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_133 = !lean_is_exclusive(x_97);
if (x_133 == 0)
{
return x_97;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_97, 0);
lean_inc(x_134);
lean_dec(x_97);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
case 2:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_136 = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(x_53);
x_137 = lean_array_push(x_35, x_53);
x_138 = lean_array_get_borrowed(x_136, x_1, x_31);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_53);
x_139 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_53, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
lean_inc(x_140);
lean_inc(x_53);
x_141 = l_Lean_mkAppB(x_85, x_53, x_140);
x_142 = lean_array_push(x_137, x_53);
x_143 = lean_array_push(x_142, x_140);
x_71 = x_31;
x_72 = x_141;
x_73 = x_143;
x_74 = x_86;
x_75 = lean_box(0);
goto block_84;
}
else
{
uint8_t x_144; 
lean_dec_ref(x_137);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_29);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_144 = !lean_is_exclusive(x_139);
if (x_144 == 0)
{
return x_139;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_139, 0);
lean_inc(x_145);
lean_dec(x_139);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_53);
x_147 = lean_ctor_get(x_138, 0);
x_148 = lean_ctor_get(x_138, 1);
lean_inc_ref(x_148);
lean_inc_ref(x_147);
x_149 = l_Lean_mkAppB(x_85, x_147, x_148);
lean_inc_ref(x_147);
x_150 = lean_array_push(x_137, x_147);
lean_inc_ref(x_148);
x_151 = lean_array_push(x_150, x_148);
x_71 = x_31;
x_72 = x_149;
x_73 = x_151;
x_74 = x_86;
x_75 = lean_box(0);
goto block_84;
}
}
default: 
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_53);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_152 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_153 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(x_152, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec_ref(x_153);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_35);
lean_ctor_set(x_154, 1, x_86);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_85);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_31);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_29);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_41);
lean_ctor_set(x_158, 1, x_157);
x_16 = x_158;
x_17 = lean_box(0);
goto block_21;
}
else
{
uint8_t x_159; 
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_29);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_159 = !lean_is_exclusive(x_153);
if (x_159 == 0)
{
return x_153;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_153, 0);
lean_inc(x_160);
lean_dec(x_153);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
block_70:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc_ref(x_60);
x_62 = l_Lean_Expr_app___override(x_57, x_60);
x_63 = lean_array_push(x_58, x_60);
x_64 = l_Lean_Expr_bindingBody_x21(x_59);
lean_dec_ref(x_59);
if (lean_is_scalar(x_37)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_37;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_34)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_34;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_32)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_32;
}
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_30)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_30;
}
lean_ctor_set(x_68, 0, x_29);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_25)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_25;
}
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_68);
x_16 = x_69;
x_17 = lean_box(0);
goto block_21;
}
block_84:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = l_Lean_Expr_bindingBody_x21(x_74);
lean_dec_ref(x_74);
x_77 = l_Lean_Expr_bindingBody_x21(x_76);
lean_dec_ref(x_76);
x_78 = lean_nat_add(x_71, x_55);
lean_dec(x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_29);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_41);
lean_ctor_set(x_83, 1, x_82);
x_16 = x_83;
x_17 = lean_box(0);
goto block_21;
}
block_94:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_array_push(x_35, x_53);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_31);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_29);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_41);
lean_ctor_set(x_93, 1, x_92);
x_16 = x_93;
x_17 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_205; 
lean_dec(x_29);
x_162 = lean_array_uget(x_2, x_4);
x_163 = lean_array_fget(x_38, x_39);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_add(x_39, x_164);
lean_dec(x_39);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_38);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_40);
lean_inc(x_162);
x_195 = l_Lean_Expr_app___override(x_33, x_162);
x_196 = l_Lean_Expr_bindingBody_x21(x_36);
lean_dec(x_36);
x_205 = lean_unbox(x_163);
lean_dec(x_163);
switch (x_205) {
case 0:
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_197 = lean_box(0);
goto block_204;
}
case 3:
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_197 = lean_box(0);
goto block_204;
}
case 5:
{
lean_object* x_206; lean_object* x_207; 
lean_inc(x_162);
x_206 = lean_array_push(x_35, x_162);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_162);
x_207 = l_Lean_Meta_Sym_inferType___redArg(x_162, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Expr_bindingDomain_x21(x_196);
x_210 = lean_expr_instantiate_rev(x_209, x_206);
lean_dec_ref(x_209);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_210);
x_211 = l_Lean_Meta_Sym_isDefEqI___redArg(x_208, x_210, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = lean_unbox(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_162);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_214 = l_Lean_Meta_trySynthInstance(x_210, x_41, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
if (lean_obj_tag(x_215) == 1)
{
lean_object* x_217; 
lean_dec(x_216);
lean_dec(x_212);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec_ref(x_215);
x_167 = x_195;
x_168 = x_206;
x_169 = x_196;
x_170 = x_217;
x_171 = lean_box(0);
goto block_180;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_215);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_218 = lean_alloc_ctor(0, 0, 1);
x_219 = lean_unbox(x_212);
lean_dec(x_212);
lean_ctor_set_uint8(x_218, 0, x_219);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_218);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_206);
lean_ctor_set(x_221, 1, x_196);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_195);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_31);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_166);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_216)) {
 x_226 = lean_alloc_ctor(0, 1, 0);
} else {
 x_226 = x_216;
}
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_212);
lean_dec_ref(x_206);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_227 = lean_ctor_get(x_214, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_228 = x_214;
} else {
 lean_dec_ref(x_214);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
return x_229;
}
}
else
{
lean_dec(x_212);
lean_dec_ref(x_210);
x_167 = x_195;
x_168 = x_206;
x_169 = x_196;
x_170 = x_162;
x_171 = lean_box(0);
goto block_180;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec_ref(x_210);
lean_dec_ref(x_206);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_162);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_230 = lean_ctor_get(x_211, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_231 = x_211;
} else {
 lean_dec_ref(x_211);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec_ref(x_206);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_162);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_233 = lean_ctor_get(x_207, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_234 = x_207;
} else {
 lean_dec_ref(x_207);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
}
case 2:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_236 = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc(x_162);
x_237 = lean_array_push(x_35, x_162);
x_238 = lean_array_get_borrowed(x_236, x_1, x_31);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_162);
x_239 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_162, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
lean_inc(x_240);
lean_inc(x_162);
x_241 = l_Lean_mkAppB(x_195, x_162, x_240);
x_242 = lean_array_push(x_237, x_162);
x_243 = lean_array_push(x_242, x_240);
x_181 = x_31;
x_182 = x_241;
x_183 = x_243;
x_184 = x_196;
x_185 = lean_box(0);
goto block_194;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_237);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_162);
lean_dec(x_31);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_244 = lean_ctor_get(x_239, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_245 = x_239;
} else {
 lean_dec_ref(x_239);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_162);
x_247 = lean_ctor_get(x_238, 0);
x_248 = lean_ctor_get(x_238, 1);
lean_inc_ref(x_248);
lean_inc_ref(x_247);
x_249 = l_Lean_mkAppB(x_195, x_247, x_248);
lean_inc_ref(x_247);
x_250 = lean_array_push(x_237, x_247);
lean_inc_ref(x_248);
x_251 = lean_array_push(x_250, x_248);
x_181 = x_31;
x_182 = x_249;
x_183 = x_251;
x_184 = x_196;
x_185 = lean_box(0);
goto block_194;
}
}
default: 
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_162);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_252 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_253 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(x_252, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec_ref(x_253);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_35);
lean_ctor_set(x_254, 1, x_196);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_195);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_31);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_166);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_41);
lean_ctor_set(x_258, 1, x_257);
x_16 = x_258;
x_17 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_259 = lean_ctor_get(x_253, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_260 = x_253;
} else {
 lean_dec_ref(x_253);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
return x_261;
}
}
}
block_180:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_inc_ref(x_170);
x_172 = l_Lean_Expr_app___override(x_167, x_170);
x_173 = lean_array_push(x_168, x_170);
x_174 = l_Lean_Expr_bindingBody_x21(x_169);
lean_dec_ref(x_169);
if (lean_is_scalar(x_37)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_37;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
if (lean_is_scalar(x_34)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_34;
}
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
if (lean_is_scalar(x_32)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_32;
}
lean_ctor_set(x_177, 0, x_31);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_30)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_30;
}
lean_ctor_set(x_178, 0, x_166);
lean_ctor_set(x_178, 1, x_177);
if (lean_is_scalar(x_25)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_25;
}
lean_ctor_set(x_179, 0, x_41);
lean_ctor_set(x_179, 1, x_178);
x_16 = x_179;
x_17 = lean_box(0);
goto block_21;
}
block_194:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = l_Lean_Expr_bindingBody_x21(x_184);
lean_dec_ref(x_184);
x_187 = l_Lean_Expr_bindingBody_x21(x_186);
lean_dec_ref(x_186);
x_188 = lean_nat_add(x_181, x_164);
lean_dec(x_181);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_166);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_41);
lean_ctor_set(x_193, 1, x_192);
x_16 = x_193;
x_17 = lean_box(0);
goto block_21;
}
block_204:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_array_push(x_35, x_162);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_31);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_166);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_41);
lean_ctor_set(x_203, 1, x_202);
x_16 = x_203;
x_17 = lean_box(0);
goto block_21;
}
}
}
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(392u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1;
x_31 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2;
x_32 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_32);
x_33 = lean_mk_array(x_32, x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_32, x_34);
lean_dec(x_32);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_33, x_35);
x_37 = lean_array_get_size(x_2);
lean_inc_ref(x_2);
x_38 = l_Array_toSubarray___redArg(x_2, x_29, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_size(x_36);
x_46 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(x_5, x_36, x_45, x_46, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_36);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_49, 1);
x_51 = lean_ctor_get(x_50, 1);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_free_object(x_47);
x_72 = lean_ctor_get(x_55, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
lean_dec(x_55);
x_74 = l_Lean_Expr_cleanupAnnotations(x_73);
x_75 = l_Lean_Expr_isApp(x_74);
if (x_75 == 0)
{
lean_dec_ref(x_74);
lean_dec(x_72);
lean_dec(x_54);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_76);
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_74);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_72);
lean_dec(x_54);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_80 = l_Lean_Expr_isApp(x_79);
if (x_80 == 0)
{
lean_dec_ref(x_79);
lean_dec_ref(x_76);
lean_dec(x_72);
lean_dec(x_54);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = l_Lean_Expr_appFnCleanup___redArg(x_79);
x_82 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
x_83 = l_Lean_Expr_isConstOf(x_81, x_82);
lean_dec_ref(x_81);
if (x_83 == 0)
{
lean_dec_ref(x_76);
lean_dec(x_72);
lean_dec(x_54);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_84 = lean_expr_instantiate_rev(x_76, x_72);
lean_dec(x_72);
lean_dec_ref(x_76);
x_85 = lean_nat_dec_lt(x_29, x_37);
if (x_85 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_56 = x_84;
x_57 = x_10;
x_58 = lean_box(0);
goto block_71;
}
else
{
if (x_85 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_56 = x_84;
x_57 = x_10;
x_58 = lean_box(0);
goto block_71;
}
else
{
size_t x_86; uint8_t x_87; 
x_86 = lean_usize_of_nat(x_37);
x_87 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(x_83, x_2, x_46, x_86);
lean_dec_ref(x_2);
if (x_87 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_56 = x_84;
x_57 = x_10;
x_58 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_88; 
x_88 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_84, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_56 = x_89;
x_57 = x_10;
x_58 = lean_box(0);
goto block_71;
}
else
{
uint8_t x_90; 
lean_dec(x_54);
lean_dec(x_10);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
return x_88;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
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
else
{
lean_object* x_93; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_93 = lean_ctor_get(x_53, 0);
lean_inc(x_93);
lean_dec_ref(x_53);
lean_ctor_set(x_47, 0, x_93);
return x_47;
}
block_71:
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_56, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = 0;
x_63 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_62);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = 0;
x_66 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_54);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_54);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_47, 0);
lean_inc(x_94);
lean_dec(x_47);
x_95 = lean_ctor_get(x_94, 1);
x_96 = lean_ctor_get(x_95, 1);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_100, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_100, 1);
lean_inc(x_115);
lean_dec(x_100);
x_116 = l_Lean_Expr_cleanupAnnotations(x_115);
x_117 = l_Lean_Expr_isApp(x_116);
if (x_117 == 0)
{
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec(x_99);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_118);
x_119 = l_Lean_Expr_appFnCleanup___redArg(x_116);
x_120 = l_Lean_Expr_isApp(x_119);
if (x_120 == 0)
{
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec(x_114);
lean_dec(x_99);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = l_Lean_Expr_appFnCleanup___redArg(x_119);
x_122 = l_Lean_Expr_isApp(x_121);
if (x_122 == 0)
{
lean_dec_ref(x_121);
lean_dec_ref(x_118);
lean_dec(x_114);
lean_dec(x_99);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = l_Lean_Expr_appFnCleanup___redArg(x_121);
x_124 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4));
x_125 = l_Lean_Expr_isConstOf(x_123, x_124);
lean_dec_ref(x_123);
if (x_125 == 0)
{
lean_dec_ref(x_118);
lean_dec(x_114);
lean_dec(x_99);
lean_dec_ref(x_2);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_126; uint8_t x_127; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_126 = lean_expr_instantiate_rev(x_118, x_114);
lean_dec(x_114);
lean_dec_ref(x_118);
x_127 = lean_nat_dec_lt(x_29, x_37);
if (x_127 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_101 = x_126;
x_102 = x_10;
x_103 = lean_box(0);
goto block_113;
}
else
{
if (x_127 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_101 = x_126;
x_102 = x_10;
x_103 = lean_box(0);
goto block_113;
}
else
{
size_t x_128; uint8_t x_129; 
x_128 = lean_usize_of_nat(x_37);
x_129 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(x_125, x_2, x_46, x_128);
lean_dec_ref(x_2);
if (x_129 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_101 = x_126;
x_102 = x_10;
x_103 = lean_box(0);
goto block_113;
}
else
{
lean_object* x_130; 
x_130 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_126, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_101 = x_131;
x_102 = x_10;
x_103 = lean_box(0);
goto block_113;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_99);
lean_dec(x_10);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
return x_134;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_135 = lean_ctor_get(x_98, 0);
lean_inc(x_135);
lean_dec_ref(x_98);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
block_113:
{
lean_object* x_104; 
x_104 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_101, x_102);
lean_dec(x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = 0;
x_108 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 1, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_99);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_137 = !lean_is_exclusive(x_47);
if (x_137 == 0)
{
return x_47;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_47, 0);
lean_inc(x_138);
lean_dec(x_47);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0;
x_27 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_26, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
x_19 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(x_2, x_3, x_4, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_2);
lean_inc_ref(x_15);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
x_17 = l_Lean_Expr_getAppNumArgs(x_1);
x_18 = lean_array_get_size(x_15);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
x_25 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(x_15, x_16, x_1, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_26 = lean_box(x_19);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 12, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_27, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 14, 3);
lean_closure_set(x_29, 0, x_18);
lean_closure_set(x_29, 1, x_15);
lean_closure_set(x_29, 2, x_16);
x_30 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_31 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_29, x_1, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_13 = l_Lean_Meta_Sym_getCongrInfo___redArg(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Meta_Sym_Simp_simpFixedPrefix(x_1, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_13);
x_20 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_15);
x_21 = l_Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_13);
x_22 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_15);
x_23 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec_ref(x_24);
x_29 = l_Lean_Meta_Sym_Simp_simpFixedPrefix(x_1, x_27, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_27);
return x_29;
}
case 2:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_24);
x_31 = l_Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_24);
x_33 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(x_1, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_simpAppArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(469u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(477u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_3, x_22);
x_24 = lean_nat_dec_lt(x_23, x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_20);
x_25 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(x_1, x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
if (x_24 == 0)
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_16 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_20, x_21, x_27, x_28, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec_ref(x_25);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_20);
x_31 = l_Lean_Meta_Sym_inferType___redArg(x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_33 = l_Lean_Meta_whnfD(x_32, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 7)
{
lean_object* x_35; lean_object* x_36; uint8_t x_49; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_36);
lean_dec_ref(x_34);
x_49 = l_Lean_Expr_hasLooseBVars(x_36);
lean_dec_ref(x_36);
if (x_49 == 0)
{
goto block_48;
}
else
{
if (x_15 == 0)
{
lean_dec_ref(x_35);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_16 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_51);
lean_dec_ref(x_30);
x_52 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_20, x_21, x_50, x_51, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_52;
}
}
else
{
goto block_48;
}
}
block_48:
{
lean_object* x_37; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_37 = l_Lean_Meta_isProp(x_35, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_21);
x_40 = lean_sym_simp(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_20, x_21, x_30, x_41, x_7, x_8, x_9, x_10, x_11, x_12);
return x_42;
}
else
{
lean_dec(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_40;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_43 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_43, 0, x_15);
x_44 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_20, x_21, x_30, x_43, x_7, x_8, x_9, x_10, x_11, x_12);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_2);
x_53 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1;
x_54 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_33);
if (x_55 == 0)
{
return x_33;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_33, 0);
lean_inc(x_56);
lean_dec(x_33);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_31;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_31, 0);
lean_inc(x_59);
lean_dec(x_31);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_25;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_2);
x_61 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2;
x_62 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_63 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(453u);
x_4 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2;
x_16 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_getAppNumArgs(x_1);
x_18 = lean_nat_dec_lt(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_nat_sub(x_17, x_2);
lean_dec(x_17);
x_20 = lean_nat_sub(x_3, x_2);
x_21 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(x_20, x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_19);
lean_dec(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_22 = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0));
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
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
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2 = _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
