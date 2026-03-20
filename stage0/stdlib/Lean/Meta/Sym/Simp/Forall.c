// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Forall
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.Simp.Result
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "p'"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 84, 71, 254, 8, 249, 37, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 208, 133, 57, 225, 251, 103, 73)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arrow"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(203, 51, 73, 212, 39, 172, 156, 118)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "arrow_congr_right"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 119, 110, 93, 174, 252, 11, 102)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 72, 118, 56, 86, 132, 84, 122)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 43, 230, 22, 134, 52, 48, 206)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "true_arrow"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 3, 129, 158, 41, 225, 71, 211)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "true_arrow_congr_right"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value),LEAN_SCALAR_PTR_LITERAL(118, 96, 91, 171, 163, 176, 69, 89)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "true_arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 117, 111, 18, 228, 157, 82, 38)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "true_arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_value),LEAN_SCALAR_PTR_LITERAL(229, 237, 254, 33, 163, 119, 59, 188)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrow_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_value),LEAN_SCALAR_PTR_LITERAL(253, 60, 249, 93, 169, 23, 87, 100)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_true_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value),LEAN_SCALAR_PTR_LITERAL(26, 244, 117, 192, 201, 44, 53, 165)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "false_arrow"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22_value),LEAN_SCALAR_PTR_LITERAL(67, 232, 237, 20, 202, 143, 10, 43)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "false_arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25_value),LEAN_SCALAR_PTR_LITERAL(249, 202, 81, 21, 94, 79, 156, 30)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "implies_congr_right"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 214, 41, 106, 32, 244, 82, 54)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallS!"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpArrow___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__6;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implies_congr_left"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(19, 33, 3, 245, 8, 162, 217, 112)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpArrow___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpForall___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpForall___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpForall___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(lean_object* v___x_9_, lean_object* v_a_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v_xs_13_, lean_object* v___x_14_, lean_object* v_a_15_, lean_object* v___x_16_, lean_object* v_a_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_prop_20_, uint8_t v___x_21_, uint8_t v___x_22_, uint8_t v___x_23_, lean_object* v___x_24_, lean_object* v_p_25_, lean_object* v_q_26_, lean_object* v_h_27_, lean_object* v___x_28_, lean_object* v___x_29_, lean_object* v___x_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v_p_x27_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_40_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0));
lean_inc_ref(v___x_9_);
v___x_41_ = l_Lean_Name_mkStr2(v___x_9_, v___x_40_);
lean_inc(v___x_11_);
lean_inc(v_a_10_);
v___x_42_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_42_, 0, v_a_10_);
lean_ctor_set(v___x_42_, 1, v___x_11_);
v___x_43_ = l_Lean_mkConst(v___x_41_, v___x_42_);
v___x_44_ = 0;
v___x_45_ = l_Lean_Expr_bvar___override(v___x_12_);
lean_inc_ref(v___x_45_);
v___x_46_ = l_Lean_mkAppN(v___x_45_, v_xs_13_);
lean_inc_ref(v___x_46_);
lean_inc_ref(v_a_15_);
lean_inc(v___x_14_);
v___x_47_ = l_Lean_mkLambda(v___x_14_, v___x_44_, v_a_15_, v___x_46_);
lean_inc(v___x_16_);
v___x_48_ = l_Lean_Expr_bvar___override(v___x_16_);
lean_inc_ref(v_a_17_);
v___x_49_ = l_Lean_mkAppB(v_a_17_, v___x_48_, v___x_45_);
v___x_50_ = l_Lean_mkLambda(v___x_18_, v___x_44_, v___x_49_, v___x_46_);
lean_inc_ref(v_a_15_);
v___x_51_ = l_Lean_mkLambda(v___x_19_, v___x_44_, v_a_15_, v___x_50_);
lean_inc_ref(v_a_15_);
v___x_52_ = l_Lean_mkLambda(v___x_14_, v___x_44_, v_a_15_, v___x_51_);
lean_inc_ref(v_p_x27_34_);
lean_inc_ref(v_prop_20_);
lean_inc_ref(v_a_17_);
lean_inc_ref(v_a_15_);
v___x_53_ = l_Lean_mkApp6(v___x_43_, v_a_15_, v_a_17_, v_prop_20_, v___x_47_, v___x_52_, v_p_x27_34_);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_16_);
lean_dec(v___x_16_);
lean_inc_ref(v___x_54_);
v___x_55_ = lean_array_push(v___x_54_, v_p_x27_34_);
v___x_56_ = l_Array_append___redArg(v___x_55_, v_xs_13_);
v___x_57_ = l_Lean_Meta_mkLambdaFVars(v___x_56_, v___x_53_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec_ref(v___x_56_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref(v___x_57_);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1));
lean_inc_ref(v___x_9_);
v___x_60_ = l_Lean_Name_mkStr2(v___x_9_, v___x_59_);
lean_inc(v___x_24_);
v___x_61_ = l_Lean_mkConst(v___x_60_, v___x_24_);
lean_inc_ref(v_h_27_);
lean_inc_ref(v_q_26_);
lean_inc_ref(v_p_25_);
lean_inc_ref(v_a_17_);
lean_inc_ref(v_a_15_);
v___x_62_ = l_Lean_mkApp5(v___x_61_, v_a_15_, v_a_17_, v_p_25_, v_q_26_, v_h_27_);
v___x_63_ = l_Lean_Meta_mkForallFVars(v_xs_13_, v___x_28_, v___x_21_, v___x_22_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref(v___x_63_);
v___x_65_ = l_Lean_Meta_mkForallFVars(v_xs_13_, v___x_29_, v___x_21_, v___x_22_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2));
v___x_68_ = l_Lean_Name_mkStr2(v___x_9_, v___x_67_);
lean_inc(v___x_24_);
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_24_);
lean_inc_ref(v_p_25_);
lean_inc_ref(v_a_17_);
lean_inc_ref(v_a_15_);
lean_inc_ref(v___x_69_);
v___x_70_ = l_Lean_mkApp3(v___x_69_, v_a_15_, v_a_17_, v_p_25_);
lean_inc_ref(v_q_26_);
lean_inc_ref(v_a_15_);
v___x_71_ = l_Lean_mkApp3(v___x_69_, v_a_15_, v_a_17_, v_q_26_);
lean_inc_ref(v_q_26_);
v___x_72_ = lean_array_push(v___x_54_, v_q_26_);
lean_inc(v_a_64_);
lean_inc_ref(v_prop_20_);
v___x_73_ = l_Lean_mkApp3(v___x_30_, v_prop_20_, v_a_64_, v_a_66_);
v___x_74_ = l_Lean_Meta_mkLambdaFVars(v___x_72_, v___x_73_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec_ref(v___x_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref(v___x_74_);
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4));
lean_inc(v___x_24_);
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_a_10_);
lean_ctor_set(v___x_77_, 1, v___x_24_);
v___x_78_ = l_Lean_mkConst(v___x_76_, v___x_77_);
lean_inc_ref(v_a_15_);
v___x_79_ = l_Lean_mkApp6(v___x_78_, v___x_31_, v_a_15_, v___x_70_, v___x_71_, v_a_58_, v___x_62_);
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5));
lean_inc_ref(v___x_32_);
v___x_81_ = l_Lean_Name_mkStr2(v___x_32_, v___x_80_);
v___x_82_ = l_Lean_mkConst(v___x_81_, v___x_11_);
v___x_83_ = l_Lean_mkAppB(v___x_82_, v_prop_20_, v_a_64_);
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6));
v___x_85_ = l_Lean_Name_mkStr2(v___x_32_, v___x_84_);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_33_);
lean_ctor_set(v___x_86_, 1, v___x_24_);
v___x_87_ = l_Lean_mkConst(v___x_85_, v___x_86_);
lean_inc_ref(v_q_26_);
lean_inc_ref(v_p_25_);
v___x_88_ = l_Lean_mkApp6(v___x_87_, v_a_15_, v_p_25_, v_a_75_, v___x_83_, v_q_26_, v___x_79_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_89_);
v___x_91_ = lean_array_push(v___x_90_, v_p_25_);
v___x_92_ = lean_array_push(v___x_91_, v_q_26_);
v___x_93_ = lean_array_push(v___x_92_, v_h_27_);
v___x_94_ = l_Lean_Meta_mkLambdaFVars(v___x_93_, v___x_88_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec_ref(v___x_93_);
return v___x_94_;
}
else
{
lean_dec_ref(v___x_71_);
lean_dec_ref(v___x_70_);
lean_dec(v_a_64_);
lean_dec_ref(v___x_62_);
lean_dec(v_a_58_);
lean_dec(v___x_33_);
lean_dec_ref(v___x_32_);
lean_dec_ref(v___x_31_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_q_26_);
lean_dec_ref(v_p_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_prop_20_);
lean_dec_ref(v_a_15_);
lean_dec(v___x_11_);
lean_dec(v_a_10_);
return v___x_74_;
}
}
else
{
lean_dec(v_a_64_);
lean_dec_ref(v___x_62_);
lean_dec(v_a_58_);
lean_dec_ref(v___x_54_);
lean_dec(v___x_33_);
lean_dec_ref(v___x_32_);
lean_dec_ref(v___x_31_);
lean_dec_ref(v___x_30_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_q_26_);
lean_dec_ref(v_p_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_prop_20_);
lean_dec_ref(v_a_17_);
lean_dec_ref(v_a_15_);
lean_dec(v___x_11_);
lean_dec(v_a_10_);
lean_dec_ref(v___x_9_);
return v___x_65_;
}
}
else
{
lean_dec_ref(v___x_62_);
lean_dec(v_a_58_);
lean_dec_ref(v___x_54_);
lean_dec(v___x_33_);
lean_dec_ref(v___x_32_);
lean_dec_ref(v___x_31_);
lean_dec_ref(v___x_30_);
lean_dec_ref(v___x_29_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_q_26_);
lean_dec_ref(v_p_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_prop_20_);
lean_dec_ref(v_a_17_);
lean_dec_ref(v_a_15_);
lean_dec(v___x_11_);
lean_dec(v_a_10_);
lean_dec_ref(v___x_9_);
return v___x_63_;
}
}
else
{
lean_dec_ref(v___x_54_);
lean_dec(v___x_33_);
lean_dec_ref(v___x_32_);
lean_dec_ref(v___x_31_);
lean_dec_ref(v___x_30_);
lean_dec_ref(v___x_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_q_26_);
lean_dec_ref(v_p_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_prop_20_);
lean_dec_ref(v_a_17_);
lean_dec_ref(v_a_15_);
lean_dec(v___x_11_);
lean_dec(v_a_10_);
lean_dec_ref(v___x_9_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed(lean_object** _args){
lean_object* v___x_95_ = _args[0];
lean_object* v_a_96_ = _args[1];
lean_object* v___x_97_ = _args[2];
lean_object* v___x_98_ = _args[3];
lean_object* v_xs_99_ = _args[4];
lean_object* v___x_100_ = _args[5];
lean_object* v_a_101_ = _args[6];
lean_object* v___x_102_ = _args[7];
lean_object* v_a_103_ = _args[8];
lean_object* v___x_104_ = _args[9];
lean_object* v___x_105_ = _args[10];
lean_object* v_prop_106_ = _args[11];
lean_object* v___x_107_ = _args[12];
lean_object* v___x_108_ = _args[13];
lean_object* v___x_109_ = _args[14];
lean_object* v___x_110_ = _args[15];
lean_object* v_p_111_ = _args[16];
lean_object* v_q_112_ = _args[17];
lean_object* v_h_113_ = _args[18];
lean_object* v___x_114_ = _args[19];
lean_object* v___x_115_ = _args[20];
lean_object* v___x_116_ = _args[21];
lean_object* v___x_117_ = _args[22];
lean_object* v___x_118_ = _args[23];
lean_object* v___x_119_ = _args[24];
lean_object* v_p_x27_120_ = _args[25];
lean_object* v___y_121_ = _args[26];
lean_object* v___y_122_ = _args[27];
lean_object* v___y_123_ = _args[28];
lean_object* v___y_124_ = _args[29];
lean_object* v___y_125_ = _args[30];
_start:
{
uint8_t v___x_2472__boxed_126_; uint8_t v___x_2473__boxed_127_; uint8_t v___x_2474__boxed_128_; lean_object* v_res_129_; 
v___x_2472__boxed_126_ = lean_unbox(v___x_107_);
v___x_2473__boxed_127_ = lean_unbox(v___x_108_);
v___x_2474__boxed_128_ = lean_unbox(v___x_109_);
v_res_129_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(v___x_95_, v_a_96_, v___x_97_, v___x_98_, v_xs_99_, v___x_100_, v_a_101_, v___x_102_, v_a_103_, v___x_104_, v___x_105_, v_prop_106_, v___x_2472__boxed_126_, v___x_2473__boxed_127_, v___x_2474__boxed_128_, v___x_110_, v_p_111_, v_q_112_, v_h_113_, v___x_114_, v___x_115_, v___x_116_, v___x_117_, v___x_118_, v___x_119_, v_p_x27_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec_ref(v_xs_99_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(lean_object* v_k_130_, lean_object* v_b_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_apply_6(v_k_130_, v_b_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_138_, lean_object* v_b_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(v_k_138_, v_b_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(lean_object* v_name_146_, uint8_t v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, uint8_t v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_156_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_156_, 0, v_k_149_);
v___x_157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_146_, v_bi_147_, v_type_148_, v___f_156_, v_kind_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_157_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_157_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___boxed(lean_object* v_name_174_, lean_object* v_bi_175_, lean_object* v_type_176_, lean_object* v_k_177_, lean_object* v_kind_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_bi_boxed_184_; uint8_t v_kind_boxed_185_; lean_object* v_res_186_; 
v_bi_boxed_184_ = lean_unbox(v_bi_175_);
v_kind_boxed_185_ = lean_unbox(v_kind_178_);
v_res_186_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_174_, v_bi_boxed_184_, v_type_176_, v_k_177_, v_kind_boxed_185_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(lean_object* v_name_187_, lean_object* v_type_188_, lean_object* v_k_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = 0;
v___x_196_ = 0;
v___x_197_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_187_, v___x_195_, v_type_188_, v_k_189_, v___x_196_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg___boxed(lean_object* v_name_198_, lean_object* v_type_199_, lean_object* v_k_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_198_, v_type_199_, v_k_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(lean_object* v_xs_213_, lean_object* v___x_214_, uint8_t v___x_215_, uint8_t v___x_216_, uint8_t v___x_217_, lean_object* v_p_218_, lean_object* v_q_219_, lean_object* v_a_220_, lean_object* v___x_221_, lean_object* v_a_222_, lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v_prop_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v___x_234_, lean_object* v_h_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_mkForallFVars(v_xs_213_, v___x_214_, v___x_215_, v___x_216_, v___x_216_, v___x_217_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref(v___x_241_);
v___x_243_ = lean_unsigned_to_nat(2u);
v___x_244_ = lean_mk_empty_array_with_capacity(v___x_243_);
lean_inc_ref(v_p_218_);
v___x_245_ = lean_array_push(v___x_244_, v_p_218_);
lean_inc_ref(v_q_219_);
v___x_246_ = lean_array_push(v___x_245_, v_q_219_);
v___x_247_ = l_Lean_Meta_mkLambdaFVars(v___x_246_, v_a_242_, v___x_215_, v___x_216_, v___x_215_, v___x_216_, v___x_217_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec_ref(v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_247_);
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0));
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1));
lean_inc(v_a_220_);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_220_);
lean_ctor_set(v___x_251_, 1, v___x_221_);
lean_inc_ref(v___x_251_);
v___x_252_ = l_Lean_mkConst(v___x_250_, v___x_251_);
lean_inc(v_a_248_);
lean_inc_ref(v_a_222_);
v___x_253_ = l_Lean_mkAppB(v___x_252_, v_a_222_, v_a_248_);
v___x_254_ = lean_box(v___x_215_);
v___x_255_ = lean_box(v___x_216_);
v___x_256_ = lean_box(v___x_217_);
lean_inc_ref(v___x_253_);
v___f_257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed), 31, 25);
lean_closure_set(v___f_257_, 0, v___x_249_);
lean_closure_set(v___f_257_, 1, v_a_220_);
lean_closure_set(v___f_257_, 2, v___x_223_);
lean_closure_set(v___f_257_, 3, v___x_224_);
lean_closure_set(v___f_257_, 4, v_xs_213_);
lean_closure_set(v___f_257_, 5, v___x_225_);
lean_closure_set(v___f_257_, 6, v_a_222_);
lean_closure_set(v___f_257_, 7, v___x_226_);
lean_closure_set(v___f_257_, 8, v_a_248_);
lean_closure_set(v___f_257_, 9, v___x_227_);
lean_closure_set(v___f_257_, 10, v___x_228_);
lean_closure_set(v___f_257_, 11, v_prop_229_);
lean_closure_set(v___f_257_, 12, v___x_254_);
lean_closure_set(v___f_257_, 13, v___x_255_);
lean_closure_set(v___f_257_, 14, v___x_256_);
lean_closure_set(v___f_257_, 15, v___x_251_);
lean_closure_set(v___f_257_, 16, v_p_218_);
lean_closure_set(v___f_257_, 17, v_q_219_);
lean_closure_set(v___f_257_, 18, v_h_235_);
lean_closure_set(v___f_257_, 19, v___x_230_);
lean_closure_set(v___f_257_, 20, v___x_231_);
lean_closure_set(v___f_257_, 21, v___x_232_);
lean_closure_set(v___f_257_, 22, v___x_253_);
lean_closure_set(v___f_257_, 23, v___x_233_);
lean_closure_set(v___f_257_, 24, v___x_234_);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3));
v___x_259_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_258_, v___x_253_, v___f_257_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_259_;
}
else
{
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec_ref(v_h_235_);
lean_dec(v___x_234_);
lean_dec_ref(v___x_233_);
lean_dec_ref(v___x_232_);
lean_dec_ref(v___x_231_);
lean_dec_ref(v___x_230_);
lean_dec_ref(v_prop_229_);
lean_dec(v___x_228_);
lean_dec(v___x_227_);
lean_dec(v___x_226_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v_a_222_);
lean_dec(v___x_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_q_219_);
lean_dec_ref(v_p_218_);
lean_dec_ref(v_xs_213_);
return v___x_247_;
}
}
else
{
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec_ref(v_h_235_);
lean_dec(v___x_234_);
lean_dec_ref(v___x_233_);
lean_dec_ref(v___x_232_);
lean_dec_ref(v___x_231_);
lean_dec_ref(v___x_230_);
lean_dec_ref(v_prop_229_);
lean_dec(v___x_228_);
lean_dec(v___x_227_);
lean_dec(v___x_226_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v_a_222_);
lean_dec(v___x_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_q_219_);
lean_dec_ref(v_p_218_);
lean_dec_ref(v_xs_213_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed(lean_object** _args){
lean_object* v_xs_260_ = _args[0];
lean_object* v___x_261_ = _args[1];
lean_object* v___x_262_ = _args[2];
lean_object* v___x_263_ = _args[3];
lean_object* v___x_264_ = _args[4];
lean_object* v_p_265_ = _args[5];
lean_object* v_q_266_ = _args[6];
lean_object* v_a_267_ = _args[7];
lean_object* v___x_268_ = _args[8];
lean_object* v_a_269_ = _args[9];
lean_object* v___x_270_ = _args[10];
lean_object* v___x_271_ = _args[11];
lean_object* v___x_272_ = _args[12];
lean_object* v___x_273_ = _args[13];
lean_object* v___x_274_ = _args[14];
lean_object* v___x_275_ = _args[15];
lean_object* v_prop_276_ = _args[16];
lean_object* v___x_277_ = _args[17];
lean_object* v___x_278_ = _args[18];
lean_object* v___x_279_ = _args[19];
lean_object* v___x_280_ = _args[20];
lean_object* v___x_281_ = _args[21];
lean_object* v_h_282_ = _args[22];
lean_object* v___y_283_ = _args[23];
lean_object* v___y_284_ = _args[24];
lean_object* v___y_285_ = _args[25];
lean_object* v___y_286_ = _args[26];
lean_object* v___y_287_ = _args[27];
_start:
{
uint8_t v___x_2761__boxed_288_; uint8_t v___x_2762__boxed_289_; uint8_t v___x_2763__boxed_290_; lean_object* v_res_291_; 
v___x_2761__boxed_288_ = lean_unbox(v___x_262_);
v___x_2762__boxed_289_ = lean_unbox(v___x_263_);
v___x_2763__boxed_290_ = lean_unbox(v___x_264_);
v_res_291_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(v_xs_260_, v___x_261_, v___x_2761__boxed_288_, v___x_2762__boxed_289_, v___x_2763__boxed_290_, v_p_265_, v_q_266_, v_a_267_, v___x_268_, v_a_269_, v___x_270_, v___x_271_, v___x_272_, v___x_273_, v___x_274_, v___x_275_, v_prop_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, v___x_281_, v_h_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v_res_291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = l_Lean_Level_ofNat(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1));
v___x_302_ = l_Lean_mkConst(v___x_301_, v___x_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(lean_object* v_p_306_, lean_object* v_xs_307_, lean_object* v_prop_308_, uint8_t v___x_309_, uint8_t v___x_310_, uint8_t v___x_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v___x_314_, lean_object* v___x_315_, lean_object* v___x_316_, lean_object* v___x_317_, lean_object* v_q_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0));
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_box(0);
v___x_327_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_328_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4);
lean_inc_ref(v_p_306_);
v___x_329_ = l_Lean_mkAppN(v_p_306_, v_xs_307_);
lean_inc_ref(v_q_318_);
v___x_330_ = l_Lean_mkAppN(v_q_318_, v_xs_307_);
lean_inc_ref(v___x_330_);
lean_inc_ref(v___x_329_);
lean_inc_ref(v_prop_308_);
v___x_331_ = l_Lean_mkApp3(v___x_328_, v_prop_308_, v___x_329_, v___x_330_);
lean_inc_ref(v___x_331_);
v___x_332_ = l_Lean_Meta_mkForallFVars(v_xs_307_, v___x_331_, v___x_309_, v___x_310_, v___x_310_, v___x_311_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___x_339_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6));
v___x_335_ = lean_box(v___x_309_);
v___x_336_ = lean_box(v___x_310_);
v___x_337_ = lean_box(v___x_311_);
v___f_338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed), 28, 22);
lean_closure_set(v___f_338_, 0, v_xs_307_);
lean_closure_set(v___f_338_, 1, v___x_331_);
lean_closure_set(v___f_338_, 2, v___x_335_);
lean_closure_set(v___f_338_, 3, v___x_336_);
lean_closure_set(v___f_338_, 4, v___x_337_);
lean_closure_set(v___f_338_, 5, v_p_306_);
lean_closure_set(v___f_338_, 6, v_q_318_);
lean_closure_set(v___f_338_, 7, v_a_312_);
lean_closure_set(v___f_338_, 8, v___x_326_);
lean_closure_set(v___f_338_, 9, v_a_313_);
lean_closure_set(v___f_338_, 10, v___x_327_);
lean_closure_set(v___f_338_, 11, v___x_314_);
lean_closure_set(v___f_338_, 12, v___x_315_);
lean_closure_set(v___f_338_, 13, v___x_325_);
lean_closure_set(v___f_338_, 14, v___x_334_);
lean_closure_set(v___f_338_, 15, v___x_316_);
lean_closure_set(v___f_338_, 16, v_prop_308_);
lean_closure_set(v___f_338_, 17, v___x_329_);
lean_closure_set(v___f_338_, 18, v___x_330_);
lean_closure_set(v___f_338_, 19, v___x_328_);
lean_closure_set(v___f_338_, 20, v___x_324_);
lean_closure_set(v___f_338_, 21, v___x_317_);
v___x_339_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_334_, v_a_333_, v___f_338_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_339_;
}
else
{
lean_dec_ref(v___x_331_);
lean_dec_ref(v___x_330_);
lean_dec_ref(v___x_329_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v_q_318_);
lean_dec(v___x_317_);
lean_dec(v___x_316_);
lean_dec(v___x_315_);
lean_dec(v___x_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_prop_308_);
lean_dec_ref(v_xs_307_);
lean_dec_ref(v_p_306_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed(lean_object** _args){
lean_object* v_p_340_ = _args[0];
lean_object* v_xs_341_ = _args[1];
lean_object* v_prop_342_ = _args[2];
lean_object* v___x_343_ = _args[3];
lean_object* v___x_344_ = _args[4];
lean_object* v___x_345_ = _args[5];
lean_object* v_a_346_ = _args[6];
lean_object* v_a_347_ = _args[7];
lean_object* v___x_348_ = _args[8];
lean_object* v___x_349_ = _args[9];
lean_object* v___x_350_ = _args[10];
lean_object* v___x_351_ = _args[11];
lean_object* v_q_352_ = _args[12];
lean_object* v___y_353_ = _args[13];
lean_object* v___y_354_ = _args[14];
lean_object* v___y_355_ = _args[15];
lean_object* v___y_356_ = _args[16];
lean_object* v___y_357_ = _args[17];
_start:
{
uint8_t v___x_2903__boxed_358_; uint8_t v___x_2904__boxed_359_; uint8_t v___x_2905__boxed_360_; lean_object* v_res_361_; 
v___x_2903__boxed_358_ = lean_unbox(v___x_343_);
v___x_2904__boxed_359_ = lean_unbox(v___x_344_);
v___x_2905__boxed_360_ = lean_unbox(v___x_345_);
v_res_361_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(v_p_340_, v_xs_341_, v_prop_342_, v___x_2903__boxed_358_, v___x_2904__boxed_359_, v___x_2905__boxed_360_, v_a_346_, v_a_347_, v___x_348_, v___x_349_, v___x_350_, v___x_351_, v_q_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(lean_object* v_xs_365_, lean_object* v_prop_366_, uint8_t v___x_367_, uint8_t v___x_368_, uint8_t v___x_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v___x_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v_p_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1));
v___x_382_ = lean_box(v___x_367_);
v___x_383_ = lean_box(v___x_368_);
v___x_384_ = lean_box(v___x_369_);
lean_inc_ref(v_a_371_);
v___f_385_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed), 18, 12);
lean_closure_set(v___f_385_, 0, v_p_375_);
lean_closure_set(v___f_385_, 1, v_xs_365_);
lean_closure_set(v___f_385_, 2, v_prop_366_);
lean_closure_set(v___f_385_, 3, v___x_382_);
lean_closure_set(v___f_385_, 4, v___x_383_);
lean_closure_set(v___f_385_, 5, v___x_384_);
lean_closure_set(v___f_385_, 6, v_a_370_);
lean_closure_set(v___f_385_, 7, v_a_371_);
lean_closure_set(v___f_385_, 8, v___x_372_);
lean_closure_set(v___f_385_, 9, v___x_373_);
lean_closure_set(v___f_385_, 10, v___x_381_);
lean_closure_set(v___f_385_, 11, v___x_374_);
v___x_386_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_381_, v_a_371_, v___f_385_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed(lean_object* v_xs_387_, lean_object* v_prop_388_, lean_object* v___x_389_, lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_p_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v___x_2998__boxed_403_; uint8_t v___x_2999__boxed_404_; uint8_t v___x_3000__boxed_405_; lean_object* v_res_406_; 
v___x_2998__boxed_403_ = lean_unbox(v___x_389_);
v___x_2999__boxed_404_ = lean_unbox(v___x_390_);
v___x_3000__boxed_405_ = lean_unbox(v___x_391_);
v_res_406_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(v_xs_387_, v_prop_388_, v___x_2998__boxed_403_, v___x_2999__boxed_404_, v___x_3000__boxed_405_, v_a_392_, v_a_393_, v___x_394_, v___x_395_, v___x_396_, v_p_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
return v_res_406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = l_Lean_Level_ofNat(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1(void){
_start:
{
lean_object* v___x_409_; lean_object* v_prop_410_; 
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v_prop_410_ = l_Lean_mkSort(v___x_409_);
return v_prop_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(lean_object* v_xs_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_prop_422_; uint8_t v___x_423_; uint8_t v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v_prop_422_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1);
v___x_423_ = 0;
v___x_424_ = 1;
v___x_425_ = 1;
v___x_426_ = l_Lean_Meta_mkForallFVars(v_xs_414_, v_prop_422_, v___x_423_, v___x_424_, v___x_424_, v___x_425_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v___x_426_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
lean_inc(v_a_416_);
lean_inc_ref(v_a_415_);
lean_inc(v_a_427_);
v___x_428_ = l_Lean_Meta_getLevel(v_a_427_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___x_435_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3));
v___x_431_ = lean_box(v___x_423_);
v___x_432_ = lean_box(v___x_424_);
v___x_433_ = lean_box(v___x_425_);
lean_inc(v_a_427_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed), 16, 10);
lean_closure_set(v___f_434_, 0, v_xs_414_);
lean_closure_set(v___f_434_, 1, v_prop_422_);
lean_closure_set(v___f_434_, 2, v___x_431_);
lean_closure_set(v___f_434_, 3, v___x_432_);
lean_closure_set(v___f_434_, 4, v___x_433_);
lean_closure_set(v___f_434_, 5, v_a_429_);
lean_closure_set(v___f_434_, 6, v_a_427_);
lean_closure_set(v___f_434_, 7, v___x_420_);
lean_closure_set(v___f_434_, 8, v___x_430_);
lean_closure_set(v___f_434_, 9, v___x_421_);
v___x_435_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_430_, v_a_427_, v___f_434_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
return v___x_435_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_a_427_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_xs_414_);
v_a_436_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_428_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_428_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_xs_414_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___boxed(lean_object* v_xs_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(lean_object* v_00_u03b1_451_, lean_object* v_name_452_, uint8_t v_bi_453_, lean_object* v_type_454_, lean_object* v_k_455_, uint8_t v_kind_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_452_, v_bi_453_, v_type_454_, v_k_455_, v_kind_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_463_, lean_object* v_name_464_, lean_object* v_bi_465_, lean_object* v_type_466_, lean_object* v_k_467_, lean_object* v_kind_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v_bi_boxed_474_; uint8_t v_kind_boxed_475_; lean_object* v_res_476_; 
v_bi_boxed_474_ = lean_unbox(v_bi_465_);
v_kind_boxed_475_ = lean_unbox(v_kind_468_);
v_res_476_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(v_00_u03b1_463_, v_name_464_, v_bi_boxed_474_, v_type_466_, v_k_467_, v_kind_boxed_475_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(lean_object* v_00_u03b1_477_, lean_object* v_name_478_, lean_object* v_type_479_, lean_object* v_k_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_478_, v_type_479_, v_k_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___boxed(lean_object* v_00_u03b1_487_, lean_object* v_name_488_, lean_object* v_type_489_, lean_object* v_k_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(v_00_u03b1_487_, v_name_488_, v_type_489_, v_k_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(lean_object* v_declName_497_, lean_object* v_us_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = l_Lean_Expr_const___override(v_declName_497_, v_us_498_);
v___x_502_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_501_, v___y_499_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg___boxed(lean_object* v_declName_503_, lean_object* v_us_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_503_, v_us_504_, v___y_505_);
lean_dec(v___y_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(lean_object* v_declName_508_, lean_object* v_us_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_508_, v_us_509_, v___y_511_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___boxed(lean_object* v_declName_518_, lean_object* v_us_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(v_declName_518_, v_us_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(lean_object* v_f_528_, lean_object* v_a_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___y_538_; lean_object* v___x_541_; uint8_t v_debug_542_; 
v___x_541_ = lean_st_ref_get(v___y_531_);
v_debug_542_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*7);
lean_dec(v___x_541_);
if (v_debug_542_ == 0)
{
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v___y_530_);
v___y_538_ = v___y_531_;
goto v___jp_537_;
}
else
{
lean_object* v___x_543_; 
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc_ref(v_f_528_);
v___x_543_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; 
lean_dec_ref(v___x_543_);
lean_inc(v___y_531_);
lean_inc_ref(v_a_529_);
v___x_544_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_dec_ref(v___x_544_);
v___y_538_ = v___y_531_;
goto v___jp_537_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___y_531_);
lean_dec_ref(v_a_529_);
lean_dec_ref(v_f_528_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_a_529_);
lean_dec_ref(v_f_528_);
v_a_553_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_543_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = l_Lean_Expr_app___override(v_f_528_, v_a_529_);
v___x_540_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_539_, v___y_538_);
lean_dec(v___y_538_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1___boxed(lean_object* v_f_561_, lean_object* v_a_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_561_, v_a_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(lean_object* v_f_571_, lean_object* v_a_u2081_572_, lean_object* v_a_u2082_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_577_);
lean_inc_ref(v___y_576_);
lean_inc(v___y_575_);
lean_inc_ref(v___y_574_);
v___x_581_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_571_, v_a_u2081_572_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_581_);
v___x_583_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_582_, v_a_u2082_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_583_;
}
else
{
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_a_u2082_573_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1___boxed(lean_object* v_f_584_, lean_object* v_a_u2081_585_, lean_object* v_a_u2082_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_f_584_, v_a_u2081_585_, v_a_u2082_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(lean_object* v_e_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; 
if (lean_obj_tag(v_e_600_) == 7)
{
lean_object* v_binderName_633_; lean_object* v_binderType_634_; lean_object* v_body_635_; uint8_t v_binderInfo_636_; uint8_t v___x_637_; 
v_binderName_633_ = lean_ctor_get(v_e_600_, 0);
v_binderType_634_ = lean_ctor_get(v_e_600_, 1);
v_body_635_ = lean_ctor_get(v_e_600_, 2);
v_binderInfo_636_ = lean_ctor_get_uint8(v_e_600_, sizeof(void*)*3 + 8);
v___x_637_ = l_Lean_Expr_hasLooseBVars(v_body_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_inc_ref(v_body_635_);
lean_inc_ref(v_binderType_634_);
lean_inc(v_binderName_633_);
lean_dec_ref(v_e_600_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
lean_inc(v_a_602_);
lean_inc_ref(v_a_601_);
v___x_638_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_body_635_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_arrow_640_; lean_object* v_infos_641_; lean_object* v_v_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_693_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v_arrow_640_ = lean_ctor_get(v_a_639_, 0);
v_infos_641_ = lean_ctor_get(v_a_639_, 1);
v_v_642_ = lean_ctor_get(v_a_639_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_693_ == 0)
{
v___x_644_ = v_a_639_;
v_isShared_645_ = v_isSharedCheck_693_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_v_642_);
lean_inc(v_infos_641_);
lean_inc(v_arrow_640_);
lean_dec(v_a_639_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_693_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; 
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
lean_inc_ref(v_binderType_634_);
v___x_646_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_634_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_649_ = lean_box(0);
lean_inc(v_v_642_);
v___x_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_650_, 0, v_v_642_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_inc(v_a_647_);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_a_647_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v___x_648_, v___x_651_, v_a_602_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref(v___x_652_);
v___x_654_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_a_653_, v_binderType_634_, v_arrow_640_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_668_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_668_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_668_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_668_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_inc(v_v_642_);
lean_inc(v_a_647_);
v___x_659_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_659_, 0, v_binderName_633_);
lean_ctor_set(v___x_659_, 1, v_a_647_);
lean_ctor_set(v___x_659_, 2, v_v_642_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*3, v_binderInfo_636_);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_infos_641_);
v___x_661_ = l_Lean_mkLevelIMax_x27(v_a_647_, v_v_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 2, v___x_661_);
lean_ctor_set(v___x_644_, 1, v___x_660_);
lean_ctor_set(v___x_644_, 0, v_a_655_);
v___x_663_ = v___x_644_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v___x_661_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_663_);
v___x_665_ = v___x_657_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_a_647_);
lean_del_object(v___x_644_);
lean_dec(v_v_642_);
lean_dec(v_infos_641_);
lean_dec(v_binderName_633_);
v_a_669_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_654_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_654_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_a_647_);
lean_del_object(v___x_644_);
lean_dec(v_v_642_);
lean_dec(v_infos_641_);
lean_dec_ref(v_arrow_640_);
lean_dec_ref(v_binderType_634_);
lean_dec(v_binderName_633_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
v_a_677_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_652_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_652_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_del_object(v___x_644_);
lean_dec(v_v_642_);
lean_dec(v_infos_641_);
lean_dec_ref(v_arrow_640_);
lean_dec_ref(v_binderType_634_);
lean_dec(v_binderName_633_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
v_a_685_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_646_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_646_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
else
{
lean_dec_ref(v_binderType_634_);
lean_dec(v_binderName_633_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v___x_638_;
}
}
else
{
lean_dec_ref(v_a_601_);
v___y_609_ = v_a_602_;
v___y_610_ = v_a_603_;
v___y_611_ = v_a_604_;
v___y_612_ = v_a_605_;
v___y_613_ = v_a_606_;
goto v___jp_608_;
}
}
else
{
lean_dec_ref(v_a_601_);
v___y_609_ = v_a_602_;
v___y_610_ = v_a_603_;
v___y_611_ = v_a_604_;
v___y_612_ = v_a_605_;
v___y_613_ = v_a_606_;
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v___x_614_; 
lean_inc_ref(v_e_600_);
v___x_614_ = l_Lean_Meta_Sym_getLevel___redArg(v_e_600_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_609_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_624_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_624_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_620_, 0, v_e_600_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
lean_ctor_set(v___x_620_, 2, v_a_615_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_622_ = v___x_617_;
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
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_e_600_);
v_a_625_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_614_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_614_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___boxed(lean_object* v_e_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(lean_object* v_x_703_, uint8_t v_bi_704_, lean_object* v_t_705_, lean_object* v_b_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___y_715_; lean_object* v___x_718_; uint8_t v_debug_719_; 
v___x_718_ = lean_st_ref_get(v___y_708_);
v_debug_719_ = lean_ctor_get_uint8(v___x_718_, sizeof(void*)*7);
lean_dec(v___x_718_);
if (v_debug_719_ == 0)
{
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v___y_707_);
v___y_715_ = v___y_708_;
goto v___jp_714_;
}
else
{
lean_object* v___x_720_; 
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc_ref(v_t_705_);
v___x_720_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_721_; 
lean_dec_ref(v___x_720_);
lean_inc(v___y_708_);
lean_inc_ref(v_b_706_);
v___x_721_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_dec_ref(v___x_721_);
v___y_715_ = v___y_708_;
goto v___jp_714_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v___y_708_);
lean_dec_ref(v_b_706_);
lean_dec_ref(v_t_705_);
lean_dec(v_x_703_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v_b_706_);
lean_dec_ref(v_t_705_);
lean_dec(v_x_703_);
v_a_730_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_720_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_720_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
v___jp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = l_Lean_Expr_forallE___override(v_x_703_, v_t_705_, v_b_706_, v_bi_704_);
v___x_717_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_716_, v___y_715_);
lean_dec(v___y_715_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0___boxed(lean_object* v_x_738_, lean_object* v_bi_739_, lean_object* v_t_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
uint8_t v_bi_boxed_749_; lean_object* v_res_750_; 
v_bi_boxed_749_ = lean_unbox(v_bi_739_);
v_res_750_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_x_738_, v_bi_boxed_749_, v_t_740_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(lean_object* v_e_751_, lean_object* v_infos_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
if (lean_obj_tag(v_infos_752_) == 1)
{
lean_object* v_head_760_; lean_object* v_tail_761_; lean_object* v_binderName_762_; uint8_t v_binderInfo_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_head_760_ = lean_ctor_get(v_infos_752_, 0);
lean_inc(v_head_760_);
v_tail_761_ = lean_ctor_get(v_infos_752_, 1);
lean_inc(v_tail_761_);
lean_dec_ref(v_infos_752_);
v_binderName_762_ = lean_ctor_get(v_head_760_, 0);
lean_inc(v_binderName_762_);
v_binderInfo_763_ = lean_ctor_get_uint8(v_head_760_, sizeof(void*)*3);
lean_dec(v_head_760_);
lean_inc_ref(v_e_751_);
v___x_764_ = l_Lean_Expr_cleanupAnnotations(v_e_751_);
v___x_765_ = l_Lean_Expr_isApp(v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v___x_764_);
lean_dec(v_binderName_762_);
lean_dec(v_tail_761_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_e_751_);
return v___x_766_;
}
else
{
lean_object* v_arg_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_arg_767_ = lean_ctor_get(v___x_764_, 1);
lean_inc_ref(v_arg_767_);
v___x_768_ = l_Lean_Expr_appFnCleanup___redArg(v___x_764_);
v___x_769_ = l_Lean_Expr_isApp(v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_768_);
lean_dec_ref(v_arg_767_);
lean_dec(v_binderName_762_);
lean_dec(v_tail_761_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_e_751_);
return v___x_770_;
}
else
{
lean_object* v_arg_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_arg_771_ = lean_ctor_get(v___x_768_, 1);
lean_inc_ref(v_arg_771_);
v___x_772_ = l_Lean_Expr_appFnCleanup___redArg(v___x_768_);
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_774_ = l_Lean_Expr_isConstOf(v___x_772_, v___x_773_);
lean_dec_ref(v___x_772_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec_ref(v_arg_771_);
lean_dec_ref(v_arg_767_);
lean_dec(v_binderName_762_);
lean_dec(v_tail_761_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_e_751_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; 
lean_dec_ref(v_e_751_);
lean_inc(v_a_758_);
lean_inc_ref(v_a_757_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
lean_inc(v_a_754_);
lean_inc_ref(v_a_753_);
v___x_776_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_arg_767_, v_tail_761_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_binderName_762_, v_binderInfo_763_, v_arg_771_, v_a_777_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
return v___x_778_;
}
else
{
lean_dec_ref(v_arg_771_);
lean_dec(v_binderName_762_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v___x_779_; 
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_infos_752_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_e_751_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall___boxed(lean_object* v_e_780_, lean_object* v_infos_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_780_, v_infos_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(lean_object* v_f_790_, lean_object* v_a_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___y_800_; lean_object* v___x_803_; uint8_t v_debug_804_; 
v___x_803_ = lean_st_ref_get(v___y_793_);
v_debug_804_ = lean_ctor_get_uint8(v___x_803_, sizeof(void*)*7);
lean_dec(v___x_803_);
if (v_debug_804_ == 0)
{
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v___y_792_);
v___y_800_ = v___y_793_;
goto v___jp_799_;
}
else
{
lean_object* v___x_805_; 
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
lean_inc_ref(v_f_790_);
v___x_805_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_790_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; 
lean_dec_ref(v___x_805_);
lean_inc(v___y_793_);
lean_inc_ref(v_a_791_);
v___x_806_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_dec_ref(v___x_806_);
v___y_800_ = v___y_793_;
goto v___jp_799_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v___y_793_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_f_790_);
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_f_790_);
v_a_815_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_805_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
v___jp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Lean_Expr_app___override(v_f_790_, v_a_791_);
v___x_802_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_801_, v___y_800_);
lean_dec(v___y_800_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(lean_object* v_f_823_, lean_object* v_a_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_823_, v_a_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(lean_object* v_f_833_, lean_object* v_a_u2081_834_, lean_object* v_a_u2082_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
v___x_846_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_833_, v_a_u2081_834_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_a_847_, v_a_u2082_835_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v___x_848_;
}
else
{
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v_a_u2082_835_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(lean_object* v_f_849_, lean_object* v_a_u2081_850_, lean_object* v_a_u2082_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v_f_849_, v_a_u2081_850_, v_a_u2082_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
return v_res_862_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7));
v___x_881_ = l_Lean_mkConst(v___x_880_, v___x_879_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_box(0);
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10));
v___x_888_ = l_Lean_mkConst(v___x_887_, v___x_886_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13));
v___x_895_ = l_Lean_mkConst(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16));
v___x_902_ = l_Lean_mkConst(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_box(0);
v___x_916_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23));
v___x_917_ = l_Lean_mkConst(v___x_916_, v___x_915_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26));
v___x_924_ = l_Lean_mkConst(v___x_923_, v___x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(lean_object* v_e_925_, lean_object* v_infos_926_, lean_object* v_simpBody_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; uint8_t v___y_967_; 
if (lean_obj_tag(v_infos_926_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_apply_11(v_simpBody_927_, v_e_925_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, lean_box(0));
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_980_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_980_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_a_972_);
lean_ctor_set(v___x_976_, 1, v_infos_926_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_971_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_971_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_head_989_ = lean_ctor_get(v_infos_926_, 0);
v_tail_990_ = lean_ctor_get(v_infos_926_, 1);
lean_inc_ref(v_e_925_);
v___x_991_ = l_Lean_Expr_cleanupAnnotations(v_e_925_);
v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_991_);
v___y_939_ = v_a_928_;
v___y_940_ = v_a_929_;
v___y_941_ = v_a_930_;
v___y_942_ = v_a_931_;
v___y_943_ = v_a_932_;
v___y_944_ = v_a_933_;
v___y_945_ = v_a_934_;
v___y_946_ = v_a_935_;
v___y_947_ = v_a_936_;
goto v___jp_938_;
}
else
{
lean_object* v_arg_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_arg_993_ = lean_ctor_get(v___x_991_, 1);
lean_inc_ref(v_arg_993_);
v___x_994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
v___x_995_ = l_Lean_Expr_isApp(v___x_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___x_994_);
lean_dec_ref(v_arg_993_);
v___y_939_ = v_a_928_;
v___y_940_ = v_a_929_;
v___y_941_ = v_a_930_;
v___y_942_ = v_a_931_;
v___y_943_ = v_a_932_;
v___y_944_ = v_a_933_;
v___y_945_ = v_a_934_;
v___y_946_ = v_a_935_;
v___y_947_ = v_a_936_;
goto v___jp_938_;
}
else
{
lean_object* v_arg_996_; lean_object* v___x_997_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; uint8_t v___y_1062_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_arg_996_ = lean_ctor_get(v___x_994_, 1);
lean_inc_ref(v_arg_996_);
v___x_997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_994_);
v___x_1087_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_1088_ = l_Lean_Expr_isConstOf(v___x_997_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
v___y_939_ = v_a_928_;
v___y_940_ = v_a_929_;
v___y_941_ = v_a_930_;
v___y_942_ = v_a_931_;
v___y_943_ = v_a_932_;
v___y_944_ = v_a_933_;
v___y_945_ = v_a_934_;
v___y_946_ = v_a_935_;
v___y_947_ = v_a_936_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1089_; 
lean_dec_ref(v_e_925_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc_ref(v_a_933_);
lean_inc(v_a_932_);
lean_inc_ref(v_a_931_);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc_ref(v_arg_996_);
v___x_1089_ = lean_sym_simp(v_arg_996_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_996_, v_a_1090_);
v___x_1092_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v___x_1091_, v_a_931_);
lean_dec_ref(v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; uint8_t v___y_1095_; uint8_t v___x_1326_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1092_);
v___x_1326_ = lean_unbox(v_a_1093_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_unbox(v_a_1093_);
lean_dec(v_a_1093_);
v___y_1095_ = v___x_1327_;
goto v___jp_1094_;
}
else
{
lean_object* v_v_1328_; uint8_t v___x_1329_; 
lean_dec(v_a_1093_);
v_v_1328_ = lean_ctor_get(v_head_989_, 2);
v___x_1329_ = l_Lean_Level_isZero(v_v_1328_);
if (v___x_1329_ == 0)
{
v___y_1095_ = v___x_1329_;
goto v___jp_1094_;
}
else
{
lean_dec_ref(v___x_997_);
lean_dec_ref(v_infos_926_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_simpBody_927_);
if (lean_obj_tag(v_a_1090_) == 0)
{
lean_object* v___x_1330_; 
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_arg_996_);
v___x_1330_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_931_);
lean_dec_ref(v_a_931_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1344_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24);
v___x_1337_ = l_Lean_Expr_app___override(v___x_1336_, v_arg_993_);
v___x_1338_ = 0;
v___x_1339_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1339_, 0, v_a_1331_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*2, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___x_1335_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1340_);
v___x_1342_ = v___x_1333_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_arg_993_);
v_a_1345_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1330_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1330_);
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
else
{
lean_object* v_proof_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1382_; 
v_proof_1353_ = lean_ctor_get(v_a_1090_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_a_1090_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_a_1090_, 0);
lean_dec(v_unused_1383_);
v___x_1355_ = v_a_1090_;
v_isShared_1356_ = v_isSharedCheck_1382_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_proof_1353_);
lean_dec(v_a_1090_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1382_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_931_);
lean_dec_ref(v_a_931_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1373_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1373_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1373_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; lean_object* v___x_1367_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27);
v___x_1364_ = l_Lean_mkApp3(v___x_1363_, v_arg_996_, v_arg_993_, v_proof_1353_);
v___x_1365_ = 0;
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1364_);
lean_ctor_set(v___x_1355_, 0, v_a_1358_);
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1358_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1364_);
v___x_1367_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*2, v___x_1365_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1362_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1368_);
v___x_1370_ = v___x_1360_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1355_);
lean_dec_ref(v_proof_1353_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
v_a_1374_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1357_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1357_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
}
v___jp_1094_:
{
lean_object* v___x_1096_; 
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc_ref(v_a_933_);
lean_inc(v_a_932_);
lean_inc_ref(v_a_931_);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc(v_tail_990_);
lean_inc_ref(v_arg_993_);
v___x_1096_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arg_993_, v_tail_990_, v_simpBody_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1325_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1096_);
v_fst_1098_ = lean_ctor_get(v_a_1097_, 0);
v_snd_1099_ = lean_ctor_get(v_a_1097_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_a_1097_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1101_ = v_a_1097_;
v_isShared_1102_ = v_isSharedCheck_1325_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snd_1099_);
lean_inc(v_fst_1098_);
lean_dec(v_a_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1325_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_993_, v_fst_1098_);
v___x_1104_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___x_1103_, v_a_931_);
lean_dec_ref(v___x_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; uint8_t v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lean_unbox(v_a_1105_);
if (v___x_1106_ == 0)
{
if (lean_obj_tag(v_a_1090_) == 0)
{
lean_dec_ref(v_a_1090_);
if (lean_obj_tag(v_fst_1098_) == 0)
{
lean_object* v___x_1107_; 
lean_dec_ref(v_fst_1098_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v___x_1107_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_996_, v_a_931_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_arg_996_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1126_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1126_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1126_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_unbox(v_a_1108_);
if (v___x_1112_ == 0)
{
uint8_t v___x_1113_; 
lean_del_object(v___x_1110_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec_ref(v_arg_993_);
v___x_1113_ = lean_unbox(v_a_1108_);
lean_dec(v_a_1108_);
v___y_967_ = v___x_1113_;
goto v___jp_966_;
}
else
{
lean_object* v_v_1114_; uint8_t v___x_1115_; 
lean_dec(v_a_1108_);
v_v_1114_ = lean_ctor_get(v_head_989_, 2);
v___x_1115_ = l_Lean_Level_isZero(v_v_1114_);
if (v___x_1115_ == 0)
{
lean_del_object(v___x_1110_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec_ref(v_arg_993_);
v___y_967_ = v___x_1115_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1121_; 
lean_dec_ref(v_infos_926_);
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8);
lean_inc_ref(v_arg_993_);
v___x_1117_ = l_Lean_Expr_app___override(v___x_1116_, v_arg_993_);
v___x_1118_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1118_, 0, v_arg_993_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*2, v___x_1119_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1118_);
v___x_1121_ = v___x_1101_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_snd_1099_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1121_);
v___x_1123_ = v___x_1110_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec_ref(v_arg_993_);
lean_dec_ref(v_infos_926_);
v_a_1127_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1107_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1107_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_e_x27_1135_; lean_object* v_proof_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1170_; 
lean_inc(v_head_989_);
lean_dec_ref(v_infos_926_);
v_e_x27_1135_ = lean_ctor_get(v_fst_1098_, 0);
v_proof_1136_ = lean_ctor_get(v_fst_1098_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_fst_1098_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1138_ = v_fst_1098_;
v_isShared_1139_ = v_isSharedCheck_1170_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_proof_1136_);
lean_inc(v_e_x27_1135_);
lean_dec(v_fst_1098_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1170_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_996_, v_a_931_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1161_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1161_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1161_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_unbox(v_a_1141_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; 
lean_del_object(v___x_1143_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
v___x_1146_ = lean_unbox(v_a_1141_);
lean_dec(v_a_1141_);
v___y_999_ = v_proof_1136_;
v___y_1000_ = v_snd_1099_;
v___y_1001_ = v_e_x27_1135_;
v___y_1002_ = v___x_1146_;
goto v___jp_998_;
}
else
{
lean_object* v_v_1147_; uint8_t v___x_1148_; 
lean_dec(v_a_1141_);
v_v_1147_ = lean_ctor_get(v_head_989_, 2);
v___x_1148_ = l_Lean_Level_isZero(v_v_1147_);
if (v___x_1148_ == 0)
{
lean_del_object(v___x_1143_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
v___y_999_ = v_proof_1136_;
v___y_1000_ = v_snd_1099_;
v___y_1001_ = v_e_x27_1135_;
v___y_1002_ = v___x_1148_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec(v_head_989_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11);
lean_inc_ref(v_e_x27_1135_);
v___x_1150_ = l_Lean_mkApp3(v___x_1149_, v_arg_993_, v_e_x27_1135_, v_proof_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1150_);
v___x_1152_ = v___x_1138_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_e_x27_1135_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
uint8_t v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*2, v___x_1153_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1152_);
v___x_1155_ = v___x_1101_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_snd_1099_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1155_);
v___x_1157_ = v___x_1143_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_del_object(v___x_1138_);
lean_dec_ref(v_proof_1136_);
lean_dec_ref(v_e_x27_1135_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v_a_1162_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1140_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1140_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
else
{
lean_inc(v_head_989_);
lean_dec_ref(v_infos_926_);
if (lean_obj_tag(v_fst_1098_) == 0)
{
lean_object* v_e_x27_1171_; lean_object* v_proof_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_fst_1098_);
v_e_x27_1171_ = lean_ctor_get(v_a_1090_, 0);
v_proof_1172_ = lean_ctor_get(v_a_1090_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_a_1090_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1174_ = v_a_1090_;
v_isShared_1175_ = v_isSharedCheck_1206_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_proof_1172_);
lean_inc(v_e_x27_1171_);
lean_dec(v_a_1090_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1206_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1171_, v_a_931_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1197_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1197_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1197_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_unbox(v_a_1177_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1182_; 
lean_del_object(v___x_1179_);
lean_del_object(v___x_1174_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
v___x_1182_ = lean_unbox(v_a_1177_);
lean_dec(v_a_1177_);
v___y_1028_ = v_e_x27_1171_;
v___y_1029_ = v_snd_1099_;
v___y_1030_ = v_proof_1172_;
v___y_1031_ = v___x_1182_;
goto v___jp_1027_;
}
else
{
lean_object* v_v_1183_; uint8_t v___x_1184_; 
lean_dec(v_a_1177_);
v_v_1183_ = lean_ctor_get(v_head_989_, 2);
v___x_1184_ = l_Lean_Level_isZero(v_v_1183_);
if (v___x_1184_ == 0)
{
lean_del_object(v___x_1179_);
lean_del_object(v___x_1174_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
v___y_1028_ = v_e_x27_1171_;
v___y_1029_ = v_snd_1099_;
v___y_1030_ = v_proof_1172_;
v___y_1031_ = v___x_1184_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_dec_ref(v_e_x27_1171_);
lean_dec_ref(v___x_997_);
lean_dec(v_head_989_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v___x_1185_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14);
lean_inc_ref(v_arg_993_);
v___x_1186_ = l_Lean_mkApp3(v___x_1185_, v_arg_996_, v_arg_993_, v_proof_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1186_);
lean_ctor_set(v___x_1174_, 0, v_arg_993_);
v___x_1188_ = v___x_1174_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_arg_993_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
uint8_t v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*2, v___x_1189_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1188_);
v___x_1191_ = v___x_1101_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_snd_1099_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1191_);
v___x_1193_ = v___x_1179_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_del_object(v___x_1174_);
lean_dec_ref(v_proof_1172_);
lean_dec_ref(v_e_x27_1171_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v_a_1198_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1176_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1176_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1207_; lean_object* v_proof_1208_; lean_object* v_e_x27_1209_; lean_object* v_proof_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1244_; 
v_e_x27_1207_ = lean_ctor_get(v_a_1090_, 0);
lean_inc_ref(v_e_x27_1207_);
v_proof_1208_ = lean_ctor_get(v_a_1090_, 1);
lean_inc_ref(v_proof_1208_);
lean_dec_ref(v_a_1090_);
v_e_x27_1209_ = lean_ctor_get(v_fst_1098_, 0);
v_proof_1210_ = lean_ctor_get(v_fst_1098_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_fst_1098_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1212_ = v_fst_1098_;
v_isShared_1213_ = v_isSharedCheck_1244_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_proof_1210_);
lean_inc(v_e_x27_1209_);
lean_dec(v_fst_1098_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1244_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1207_, v_a_931_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1235_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1235_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1235_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_unbox(v_a_1215_);
if (v___x_1219_ == 0)
{
uint8_t v___x_1220_; 
lean_del_object(v___x_1217_);
lean_del_object(v___x_1212_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
v___x_1220_ = lean_unbox(v_a_1215_);
lean_dec(v_a_1215_);
v___y_1057_ = v_e_x27_1209_;
v___y_1058_ = v_e_x27_1207_;
v___y_1059_ = v_snd_1099_;
v___y_1060_ = v_proof_1208_;
v___y_1061_ = v_proof_1210_;
v___y_1062_ = v___x_1220_;
goto v___jp_1056_;
}
else
{
lean_object* v_v_1221_; uint8_t v___x_1222_; 
lean_dec(v_a_1215_);
v_v_1221_ = lean_ctor_get(v_head_989_, 2);
v___x_1222_ = l_Lean_Level_isZero(v_v_1221_);
if (v___x_1222_ == 0)
{
lean_del_object(v___x_1217_);
lean_del_object(v___x_1212_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
v___y_1057_ = v_e_x27_1209_;
v___y_1058_ = v_e_x27_1207_;
v___y_1059_ = v_snd_1099_;
v___y_1060_ = v_proof_1208_;
v___y_1061_ = v_proof_1210_;
v___y_1062_ = v___x_1222_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_dec_ref(v_e_x27_1207_);
lean_dec_ref(v___x_997_);
lean_dec(v_head_989_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v___x_1223_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17);
lean_inc_ref(v_e_x27_1209_);
v___x_1224_ = l_Lean_mkApp5(v___x_1223_, v_arg_996_, v_arg_993_, v_e_x27_1209_, v_proof_1208_, v_proof_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1224_);
v___x_1226_ = v___x_1212_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_e_x27_1209_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
uint8_t v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*2, v___x_1227_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1226_);
v___x_1229_ = v___x_1101_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_snd_1099_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1229_);
v___x_1231_ = v___x_1217_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
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
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_del_object(v___x_1212_);
lean_dec_ref(v_proof_1210_);
lean_dec_ref(v_e_x27_1209_);
lean_dec_ref(v_proof_1208_);
lean_dec_ref(v_e_x27_1207_);
lean_dec(v_a_1105_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v_a_1236_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1214_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1214_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1314_; 
lean_inc(v_head_989_);
lean_dec(v_a_1105_);
lean_dec(v_snd_1099_);
lean_dec(v_a_1090_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_infos_926_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; lean_object* v_unused_1316_; 
v_unused_1315_ = lean_ctor_get(v_infos_926_, 1);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_infos_926_, 0);
lean_dec(v_unused_1316_);
v___x_1246_ = v_infos_926_;
v_isShared_1247_ = v_isSharedCheck_1314_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v_infos_926_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1314_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
if (lean_obj_tag(v_fst_1098_) == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref(v_fst_1098_);
lean_dec_ref(v_arg_993_);
v___x_1248_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_931_);
lean_dec_ref(v_a_931_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1268_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1268_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1268_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_u_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_u_1253_ = lean_ctor_get(v_head_989_, 1);
lean_inc(v_u_1253_);
lean_dec(v_head_989_);
v___x_1254_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19));
v___x_1255_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1255_);
lean_ctor_set(v___x_1246_, 0, v_u_1253_);
v___x_1257_ = v___x_1246_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_u_1253_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1258_ = l_Lean_mkConst(v___x_1254_, v___x_1257_);
v___x_1259_ = l_Lean_Expr_app___override(v___x_1258_, v_arg_996_);
v___x_1260_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1260_, 0, v_a_1249_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*2, v___y_1095_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1255_);
lean_ctor_set(v___x_1101_, 0, v___x_1260_);
v___x_1262_ = v___x_1101_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1255_);
v___x_1262_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1262_);
v___x_1264_ = v___x_1251_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
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
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1246_);
lean_del_object(v___x_1101_);
lean_dec_ref(v_arg_996_);
lean_dec(v_head_989_);
v_a_1269_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1248_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1248_);
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
else
{
lean_object* v_proof_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1312_; 
v_proof_1277_ = lean_ctor_get(v_fst_1098_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_fst_1098_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_fst_1098_, 0);
lean_dec(v_unused_1313_);
v___x_1279_ = v_fst_1098_;
v_isShared_1280_ = v_isSharedCheck_1312_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_proof_1277_);
lean_dec(v_fst_1098_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1312_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_931_);
lean_dec_ref(v_a_931_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1303_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1303_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1303_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_u_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v_u_1286_ = lean_ctor_get(v_head_989_, 1);
lean_inc(v_u_1286_);
lean_dec(v_head_989_);
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21));
v___x_1288_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1288_);
lean_ctor_set(v___x_1246_, 0, v_u_1286_);
v___x_1290_ = v___x_1246_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_u_1286_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1291_ = l_Lean_mkConst(v___x_1287_, v___x_1290_);
v___x_1292_ = l_Lean_mkApp3(v___x_1291_, v_arg_996_, v_arg_993_, v_proof_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1292_);
lean_ctor_set(v___x_1279_, 0, v_a_1282_);
v___x_1294_ = v___x_1279_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1282_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*2, v___y_1095_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1288_);
lean_ctor_set(v___x_1101_, 0, v___x_1294_);
v___x_1296_ = v___x_1101_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1288_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1296_);
v___x_1298_ = v___x_1284_;
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
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_del_object(v___x_1279_);
lean_dec_ref(v_proof_1277_);
lean_del_object(v___x_1246_);
lean_del_object(v___x_1101_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
v_a_1304_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1281_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1281_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
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
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec(v_fst_1098_);
lean_dec(v_a_1090_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec_ref(v_infos_926_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
v_a_1317_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1104_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1104_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_dec(v_a_1090_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec_ref(v_infos_926_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_a_1090_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec_ref(v_infos_926_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_simpBody_927_);
v_a_1384_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1092_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1092_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec_ref(v_infos_926_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_simpBody_927_);
v_a_1392_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1089_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1089_);
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
v___jp_998_:
{
lean_object* v___x_1003_; 
lean_inc_ref(v___y_1001_);
lean_inc_ref(v_arg_996_);
lean_inc_ref(v___x_997_);
v___x_1003_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_997_, v_arg_996_, v___y_1001_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1018_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1018_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1018_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1));
v___x_1009_ = l_Lean_Expr_constLevels_x21(v___x_997_);
lean_dec_ref(v___x_997_);
v___x_1010_ = l_Lean_mkConst(v___x_1008_, v___x_1009_);
v___x_1011_ = l_Lean_mkApp4(v___x_1010_, v_arg_996_, v_arg_993_, v___y_1001_, v___y_999_);
v___x_1012_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1012_, 0, v_a_1004_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*2, v___y_1002_);
v___x_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_head_989_);
lean_ctor_set(v___x_1013_, 1, v___y_1000_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1014_);
v___x_1016_ = v___x_1006_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
v_a_1019_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1003_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1003_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1032_; 
lean_inc_ref(v_arg_993_);
lean_inc_ref(v___y_1028_);
lean_inc_ref(v___x_997_);
v___x_1032_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_997_, v___y_1028_, v_arg_993_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1047_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3));
v___x_1038_ = l_Lean_Expr_constLevels_x21(v___x_997_);
lean_dec_ref(v___x_997_);
v___x_1039_ = l_Lean_mkConst(v___x_1037_, v___x_1038_);
v___x_1040_ = l_Lean_mkApp4(v___x_1039_, v_arg_996_, v___y_1028_, v_arg_993_, v___y_1030_);
v___x_1041_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1041_, 0, v_a_1033_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*2, v___y_1031_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_head_989_);
lean_ctor_set(v___x_1042_, 1, v___y_1029_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1043_);
v___x_1045_ = v___x_1035_;
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
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
v_a_1048_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1032_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1032_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
v___jp_1056_:
{
lean_object* v___x_1063_; 
lean_inc_ref(v___y_1057_);
lean_inc_ref(v___y_1058_);
lean_inc_ref(v___x_997_);
v___x_1063_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_997_, v___y_1058_, v___y_1057_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1078_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1078_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1078_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5));
v___x_1069_ = l_Lean_Expr_constLevels_x21(v___x_997_);
lean_dec_ref(v___x_997_);
v___x_1070_ = l_Lean_mkConst(v___x_1068_, v___x_1069_);
v___x_1071_ = l_Lean_mkApp6(v___x_1070_, v_arg_996_, v___y_1058_, v_arg_993_, v___y_1057_, v___y_1060_, v___y_1061_);
v___x_1072_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1072_, 0, v_a_1064_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*2, v___y_1062_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_head_989_);
lean_ctor_set(v___x_1073_, 1, v___y_1059_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1074_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_993_);
lean_dec(v_head_989_);
v_a_1079_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1063_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1063_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
}
v___jp_938_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_apply_11(v_simpBody_927_, v_e_925_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, lean_box(0));
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_957_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_a_949_);
lean_ctor_set(v___x_953_, 1, v_infos_926_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_infos_926_);
v_a_958_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_948_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_948_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_968_, 0, v___y_967_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_infos_926_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___boxed(lean_object* v_e_1400_, lean_object* v_infos_1401_, lean_object* v_simpBody_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_e_1400_, v_infos_1401_, v_simpBody_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(lean_object* v_f_1414_, lean_object* v_a_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_1414_, v_a_1415_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___boxed(lean_object* v_f_1427_, lean_object* v_a_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(v_f_1427_, v_a_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object* v_simpBody_1447_, lean_object* v_e_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = l_Lean_Expr_isArrow(v_e_1448_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_e_1448_);
lean_dec_ref(v_simpBody_1447_);
v___x_1460_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; 
lean_inc(v_a_1457_);
lean_inc_ref(v_a_1456_);
lean_inc(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
lean_inc_ref(v_e_1448_);
v___x_1462_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_1448_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_arrow_1464_; lean_object* v_infos_1465_; lean_object* v_v_1466_; lean_object* v___x_1467_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v_arrow_1464_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_ref(v_arrow_1464_);
v_infos_1465_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_infos_1465_);
v_v_1466_ = lean_ctor_get(v_a_1463_, 2);
lean_inc(v_v_1466_);
lean_dec(v_a_1463_);
lean_inc(v_a_1457_);
lean_inc_ref(v_a_1456_);
lean_inc(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
lean_inc_ref(v_arrow_1464_);
v___x_1467_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arrow_1464_, v_infos_1465_, v_simpBody_1447_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1523_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1523_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1523_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_fst_1472_; 
v_fst_1472_ = lean_ctor_get(v_a_1468_, 0);
lean_inc(v_fst_1472_);
if (lean_obj_tag(v_fst_1472_) == 1)
{
lean_object* v_snd_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1517_; 
lean_del_object(v___x_1470_);
v_snd_1473_ = lean_ctor_get(v_a_1468_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_a_1468_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_a_1468_, 0);
lean_dec(v_unused_1518_);
v___x_1475_ = v_a_1468_;
v_isShared_1476_ = v_isSharedCheck_1517_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snd_1473_);
lean_dec(v_a_1468_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1517_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_e_x27_1477_; lean_object* v_proof_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1516_; 
v_e_x27_1477_ = lean_ctor_get(v_fst_1472_, 0);
v_proof_1478_ = lean_ctor_get(v_fst_1472_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_fst_1472_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1480_ = v_fst_1472_;
v_isShared_1481_ = v_isSharedCheck_1516_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_proof_1478_);
lean_inc(v_e_x27_1477_);
lean_dec(v_fst_1472_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1516_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; 
lean_inc_ref(v_e_x27_1477_);
v___x_1482_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_x27_1477_, v_snd_1473_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1507_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1507_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1507_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_inc(v_v_1466_);
v___x_1487_ = l_Lean_mkSort(v_v_1466_);
v___x_1488_ = l_Lean_Level_succ___override(v_v_1466_);
v___x_1489_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1));
v___x_1490_ = lean_box(0);
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 1);
lean_ctor_set(v___x_1475_, 1, v___x_1490_);
lean_ctor_set(v___x_1475_, 0, v___x_1488_);
v___x_1492_ = v___x_1475_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_inc_ref(v___x_1492_);
v___x_1493_ = l_Lean_mkConst(v___x_1489_, v___x_1492_);
v___x_1494_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2));
v___x_1495_ = l_Lean_mkConst(v___x_1494_, v___x_1492_);
lean_inc_ref(v_arrow_1464_);
lean_inc_ref(v___x_1487_);
lean_inc_ref(v___x_1495_);
v___x_1496_ = l_Lean_mkAppB(v___x_1495_, v___x_1487_, v_arrow_1464_);
lean_inc_ref(v_e_x27_1477_);
lean_inc_ref(v_e_1448_);
lean_inc_ref(v___x_1487_);
lean_inc_ref(v___x_1493_);
v___x_1497_ = l_Lean_mkApp6(v___x_1493_, v___x_1487_, v_e_1448_, v_arrow_1464_, v_e_x27_1477_, v___x_1496_, v_proof_1478_);
lean_inc(v_a_1483_);
lean_inc_ref(v___x_1487_);
v___x_1498_ = l_Lean_mkAppB(v___x_1495_, v___x_1487_, v_a_1483_);
lean_inc(v_a_1483_);
v___x_1499_ = l_Lean_mkApp6(v___x_1493_, v___x_1487_, v_e_1448_, v_e_x27_1477_, v_a_1483_, v___x_1497_, v___x_1498_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1499_);
lean_ctor_set(v___x_1480_, 0, v_a_1483_);
v___x_1501_ = v___x_1480_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1483_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*2, v___x_1459_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1501_);
v___x_1503_ = v___x_1485_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_del_object(v___x_1480_);
lean_dec_ref(v_proof_1478_);
lean_dec_ref(v_e_x27_1477_);
lean_del_object(v___x_1475_);
lean_dec(v_v_1466_);
lean_dec_ref(v_arrow_1464_);
lean_dec_ref(v_e_1448_);
v_a_1508_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1482_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1482_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
lean_dec(v_fst_1472_);
lean_dec(v_a_1468_);
lean_dec(v_v_1466_);
lean_dec_ref(v_arrow_1464_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v_e_1448_);
v___x_1519_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1519_, 0, v___x_1459_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1519_);
v___x_1521_ = v___x_1470_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_v_1466_);
lean_dec_ref(v_arrow_1464_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v_e_1448_);
v_a_1524_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1467_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1467_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_e_1448_);
lean_dec_ref(v_simpBody_1447_);
v_a_1532_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1462_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1462_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed(lean_object* v_simpBody_1540_, lean_object* v_e_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v_simpBody_1540_, v_e_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(lean_object* v_x_1553_, uint8_t v_bi_1554_, lean_object* v_t_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___y_1565_; lean_object* v___x_1568_; uint8_t v_debug_1569_; 
v___x_1568_ = lean_st_ref_get(v___y_1558_);
v_debug_1569_ = lean_ctor_get_uint8(v___x_1568_, sizeof(void*)*7);
lean_dec(v___x_1568_);
if (v_debug_1569_ == 0)
{
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v___y_1557_);
v___y_1565_ = v___y_1558_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1570_; 
lean_inc(v___y_1562_);
lean_inc_ref(v___y_1561_);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc_ref(v_t_1555_);
v___x_1570_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1555_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref(v___x_1570_);
lean_inc(v___y_1558_);
lean_inc_ref(v_b_1556_);
v___x_1571_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref(v___x_1571_);
v___y_1565_ = v___y_1558_;
goto v___jp_1564_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v___y_1558_);
lean_dec_ref(v_b_1556_);
lean_dec_ref(v_t_1555_);
lean_dec(v_x_1553_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v_b_1556_);
lean_dec_ref(v_t_1555_);
lean_dec(v_x_1553_);
v_a_1580_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1570_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1570_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
v___jp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = l_Lean_Expr_forallE___override(v_x_1553_, v_t_1555_, v_b_1556_, v_bi_1554_);
v___x_1567_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1566_, v___y_1565_);
lean_dec(v___y_1565_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg___boxed(lean_object* v_x_1588_, lean_object* v_bi_1589_, lean_object* v_t_1590_, lean_object* v_b_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_bi_boxed_1599_; lean_object* v_res_1600_; 
v_bi_boxed_1599_ = lean_unbox(v_bi_1589_);
v_res_1600_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1588_, v_bi_boxed_1599_, v_t_1590_, v_b_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(lean_object* v_x_1601_, uint8_t v_bi_1602_, lean_object* v_t_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1601_, v_bi_1602_, v_t_1603_, v_b_1604_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___boxed(lean_object* v_x_1616_, lean_object* v_bi_1617_, lean_object* v_t_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v_bi_boxed_1630_; lean_object* v_res_1631_; 
v_bi_boxed_1630_ = lean_unbox(v_bi_1617_);
v_res_1631_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(v_x_1616_, v_bi_boxed_1630_, v_t_1618_, v_b_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1631_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(lean_object* v_msg_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_toApplicative_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1716_; 
v___x_1648_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0);
v___x_1649_ = l_ReaderT_instMonad___redArg(v___x_1648_);
v_toApplicative_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v___x_1649_, 1);
lean_dec(v_unused_1717_);
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1716_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_toApplicative_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1716_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_toFunctor_1654_; lean_object* v_toSeq_1655_; lean_object* v_toSeqLeft_1656_; lean_object* v_toSeqRight_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1714_; 
v_toFunctor_1654_ = lean_ctor_get(v_toApplicative_1650_, 0);
v_toSeq_1655_ = lean_ctor_get(v_toApplicative_1650_, 2);
v_toSeqLeft_1656_ = lean_ctor_get(v_toApplicative_1650_, 3);
v_toSeqRight_1657_ = lean_ctor_get(v_toApplicative_1650_, 4);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_toApplicative_1650_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_toApplicative_1650_, 1);
lean_dec(v_unused_1715_);
v___x_1659_ = v_toApplicative_1650_;
v_isShared_1660_ = v_isSharedCheck_1714_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_toSeqRight_1657_);
lean_inc(v_toSeqLeft_1656_);
lean_inc(v_toSeq_1655_);
lean_inc(v_toFunctor_1654_);
lean_dec(v_toApplicative_1650_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1714_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___f_1668_; lean_object* v___x_1670_; 
v___f_1661_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1));
v___f_1662_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1654_);
v___f_1663_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1663_, 0, v_toFunctor_1654_);
v___f_1664_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1664_, 0, v_toFunctor_1654_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___f_1663_);
lean_ctor_set(v___x_1665_, 1, v___f_1664_);
v___f_1666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1666_, 0, v_toSeqRight_1657_);
v___f_1667_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1667_, 0, v_toSeqLeft_1656_);
v___f_1668_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1668_, 0, v_toSeq_1655_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v___f_1666_);
lean_ctor_set(v___x_1659_, 3, v___f_1667_);
lean_ctor_set(v___x_1659_, 2, v___f_1668_);
lean_ctor_set(v___x_1659_, 1, v___f_1661_);
lean_ctor_set(v___x_1659_, 0, v___x_1665_);
v___x_1670_ = v___x_1659_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___f_1661_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v___f_1668_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v___f_1667_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v___f_1666_);
v___x_1670_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v___f_1662_);
lean_ctor_set(v___x_1652_, 0, v___x_1670_);
v___x_1672_ = v___x_1652_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___f_1662_);
v___x_1672_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v_toApplicative_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1710_; 
v___x_1673_ = l_ReaderT_instMonad___redArg(v___x_1672_);
v_toApplicative_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1673_, 1);
lean_dec(v_unused_1711_);
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1710_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_toApplicative_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1710_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_toFunctor_1678_; lean_object* v_toSeq_1679_; lean_object* v_toSeqLeft_1680_; lean_object* v_toSeqRight_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1708_; 
v_toFunctor_1678_ = lean_ctor_get(v_toApplicative_1674_, 0);
v_toSeq_1679_ = lean_ctor_get(v_toApplicative_1674_, 2);
v_toSeqLeft_1680_ = lean_ctor_get(v_toApplicative_1674_, 3);
v_toSeqRight_1681_ = lean_ctor_get(v_toApplicative_1674_, 4);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_toApplicative_1674_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_toApplicative_1674_, 1);
lean_dec(v_unused_1709_);
v___x_1683_ = v_toApplicative_1674_;
v_isShared_1684_ = v_isSharedCheck_1708_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_toSeqRight_1681_);
lean_inc(v_toSeqLeft_1680_);
lean_inc(v_toSeq_1679_);
lean_inc(v_toFunctor_1678_);
lean_dec(v_toApplicative_1674_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1708_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___x_1694_; 
v___f_1685_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3));
v___f_1686_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1678_);
v___f_1687_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1687_, 0, v_toFunctor_1678_);
v___f_1688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1688_, 0, v_toFunctor_1678_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___f_1687_);
lean_ctor_set(v___x_1689_, 1, v___f_1688_);
v___f_1690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1690_, 0, v_toSeqRight_1681_);
v___f_1691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1691_, 0, v_toSeqLeft_1680_);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toSeq_1679_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 4, v___f_1690_);
lean_ctor_set(v___x_1683_, 3, v___f_1691_);
lean_ctor_set(v___x_1683_, 2, v___f_1692_);
lean_ctor_set(v___x_1683_, 1, v___f_1685_);
lean_ctor_set(v___x_1683_, 0, v___x_1689_);
v___x_1694_ = v___x_1683_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___f_1685_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v___f_1692_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v___f_1691_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v___f_1690_);
v___x_1694_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___f_1686_);
lean_ctor_set(v___x_1676_, 0, v___x_1694_);
v___x_1696_ = v___x_1676_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___f_1686_);
v___x_1696_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_22360__overap_1704_; lean_object* v___x_1705_; 
v___x_1697_ = l_ReaderT_instMonad___redArg(v___x_1696_);
v___x_1698_ = l_ReaderT_instMonad___redArg(v___x_1697_);
v___x_1699_ = l_ReaderT_instMonad___redArg(v___x_1698_);
v___x_1700_ = l_ReaderT_instMonad___redArg(v___x_1699_);
v___x_1701_ = l_ReaderT_instMonad___redArg(v___x_1700_);
v___x_1702_ = l_Lean_instInhabitedExpr;
v___x_1703_ = l_instInhabitedOfMonad___redArg(v___x_1701_, v___x_1702_);
v___x_22360__overap_1704_ = lean_panic_fn(v___x_1703_, v_msg_1637_);
v___x_1705_ = lean_apply_10(v___x_22360__overap_1704_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, lean_box(0));
return v___x_1705_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___boxed(lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v_res_1729_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__6(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1738_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__5));
v___x_1739_ = lean_unsigned_to_nat(31u);
v___x_1740_ = lean_unsigned_to_nat(160u);
v___x_1741_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__4));
v___x_1742_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__3));
v___x_1743_ = l_mkPanicMessageWithDecl(v___x_1742_, v___x_1741_, v___x_1740_, v___x_1739_, v___x_1738_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow(lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_p_1761_; lean_object* v___x_1762_; 
v_p_1761_ = l_Lean_Expr_bindingDomain_x21(v_e_1750_);
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc(v_a_1755_);
lean_inc_ref(v_a_1754_);
lean_inc(v_a_1753_);
lean_inc_ref(v_a_1752_);
lean_inc(v_a_1751_);
lean_inc_ref(v_p_1761_);
v___x_1762_ = lean_sym_simp(v_p_1761_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v_q_1764_; lean_object* v___x_1765_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
v_q_1764_ = l_Lean_Expr_bindingBody_x21(v_e_1750_);
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc(v_a_1755_);
lean_inc_ref(v_a_1754_);
lean_inc(v_a_1753_);
lean_inc_ref(v_a_1752_);
lean_inc(v_a_1751_);
lean_inc_ref(v_q_1764_);
v___x_1765_ = lean_sym_simp(v_q_1764_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1765_) == 0)
{
if (lean_obj_tag(v_a_1763_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_a_1763_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1841_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1841_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec_ref(v_a_1766_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v___x_1770_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__0));
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1770_);
v___x_1772_ = v___x_1768_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
else
{
lean_object* v_e_x27_1774_; lean_object* v_proof_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1840_; 
lean_del_object(v___x_1768_);
v_e_x27_1774_ = lean_ctor_get(v_a_1766_, 0);
v_proof_1775_ = lean_ctor_get(v_a_1766_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1766_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1777_ = v_a_1766_;
v_isShared_1778_ = v_isSharedCheck_1840_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_proof_1775_);
lean_inc(v_e_x27_1774_);
lean_dec(v_a_1766_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1840_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; 
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc_ref(v_p_1761_);
v___x_1779_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1761_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc_ref(v_q_1764_);
v___x_1781_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1764_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1823_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1823_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1823_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v_a_1787_; lean_object* v___y_1802_; 
if (lean_obj_tag(v_e_1750_) == 7)
{
lean_object* v_binderName_1812_; lean_object* v_binderType_1813_; lean_object* v_body_1814_; uint8_t v_binderInfo_1815_; uint8_t v___y_1817_; uint8_t v___x_1819_; 
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
v_binderName_1812_ = lean_ctor_get(v_e_1750_, 0);
v_binderType_1813_ = lean_ctor_get(v_e_1750_, 1);
v_body_1814_ = lean_ctor_get(v_e_1750_, 2);
v_binderInfo_1815_ = lean_ctor_get_uint8(v_e_1750_, sizeof(void*)*3 + 8);
v___x_1819_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1813_, v_p_1761_);
if (v___x_1819_ == 0)
{
v___y_1817_ = v___x_1819_;
goto v___jp_1816_;
}
else
{
uint8_t v___x_1820_; 
v___x_1820_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1814_, v_e_x27_1774_);
v___y_1817_ = v___x_1820_;
goto v___jp_1816_;
}
v___jp_1816_:
{
if (v___y_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_inc(v_binderName_1812_);
lean_dec_ref(v_e_1750_);
lean_inc_ref(v_e_x27_1774_);
lean_inc_ref(v_p_1761_);
v___x_1818_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1812_, v_binderInfo_1815_, v_p_1761_, v_e_x27_1774_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
v___y_1802_ = v___x_1818_;
goto v___jp_1801_;
}
else
{
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
v_a_1787_ = v_e_1750_;
goto v___jp_1786_;
}
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v_e_1750_);
v___x_1821_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__6, &l_Lean_Meta_Sym_Simp_simpArrow___closed__6_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__6);
v___x_1822_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1821_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
v___y_1802_ = v___x_1822_;
goto v___jp_1801_;
}
v___jp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1796_; 
v___x_1788_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__2));
v___x_1789_ = lean_box(0);
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1782_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_a_1780_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_mkConst(v___x_1788_, v___x_1791_);
v___x_1793_ = l_Lean_mkApp4(v___x_1792_, v_p_1761_, v_q_1764_, v_e_x27_1774_, v_proof_1775_);
v___x_1794_ = 0;
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v___x_1793_);
lean_ctor_set(v___x_1777_, 0, v_a_1787_);
v___x_1796_ = v___x_1777_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1787_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v___x_1793_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*2, v___x_1794_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1796_);
v___x_1798_ = v___x_1784_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
v___jp_1801_:
{
if (lean_obj_tag(v___y_1802_) == 0)
{
lean_object* v_a_1803_; 
v_a_1803_ = lean_ctor_get(v___y_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___y_1802_);
v_a_1787_ = v_a_1803_;
goto v___jp_1786_;
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_del_object(v___x_1784_);
lean_dec(v_a_1782_);
lean_dec(v_a_1780_);
lean_del_object(v___x_1777_);
lean_dec_ref(v_proof_1775_);
lean_dec_ref(v_e_x27_1774_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
v_a_1804_ = lean_ctor_get(v___y_1802_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___y_1802_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___y_1802_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___y_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1780_);
lean_del_object(v___x_1777_);
lean_dec_ref(v_proof_1775_);
lean_dec_ref(v_e_x27_1774_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v_a_1824_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1781_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1781_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_del_object(v___x_1777_);
lean_dec_ref(v_proof_1775_);
lean_dec_ref(v_e_x27_1774_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v_a_1832_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1779_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1779_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1765_);
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_object* v_e_x27_1843_; lean_object* v_proof_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_a_1842_);
v_e_x27_1843_ = lean_ctor_get(v_a_1763_, 0);
v_proof_1844_ = lean_ctor_get(v_a_1763_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_a_1763_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1846_ = v_a_1763_;
v_isShared_1847_ = v_isSharedCheck_1909_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_proof_1844_);
lean_inc(v_e_x27_1843_);
lean_dec(v_a_1763_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1909_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; 
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc_ref(v_p_1761_);
v___x_1848_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1761_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc_ref(v_q_1764_);
v___x_1850_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1764_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1892_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1892_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1892_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_a_1856_; lean_object* v___y_1871_; 
if (lean_obj_tag(v_e_1750_) == 7)
{
lean_object* v_binderName_1881_; lean_object* v_binderType_1882_; lean_object* v_body_1883_; uint8_t v_binderInfo_1884_; uint8_t v___y_1886_; uint8_t v___x_1888_; 
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
v_binderName_1881_ = lean_ctor_get(v_e_1750_, 0);
v_binderType_1882_ = lean_ctor_get(v_e_1750_, 1);
v_body_1883_ = lean_ctor_get(v_e_1750_, 2);
v_binderInfo_1884_ = lean_ctor_get_uint8(v_e_1750_, sizeof(void*)*3 + 8);
v___x_1888_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1882_, v_e_x27_1843_);
if (v___x_1888_ == 0)
{
v___y_1886_ = v___x_1888_;
goto v___jp_1885_;
}
else
{
uint8_t v___x_1889_; 
v___x_1889_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1883_, v_q_1764_);
v___y_1886_ = v___x_1889_;
goto v___jp_1885_;
}
v___jp_1885_:
{
if (v___y_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_inc(v_binderName_1881_);
lean_dec_ref(v_e_1750_);
lean_inc_ref(v_q_1764_);
lean_inc_ref(v_e_x27_1843_);
v___x_1887_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1881_, v_binderInfo_1884_, v_e_x27_1843_, v_q_1764_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
v___y_1871_ = v___x_1887_;
goto v___jp_1870_;
}
else
{
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
v_a_1856_ = v_e_1750_;
goto v___jp_1855_;
}
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v_e_1750_);
v___x_1890_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__6, &l_Lean_Meta_Sym_Simp_simpArrow___closed__6_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__6);
v___x_1891_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1890_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
v___y_1871_ = v___x_1891_;
goto v___jp_1870_;
}
v___jp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; lean_object* v___x_1865_; 
v___x_1857_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__8));
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1851_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1860_, 0, v_a_1849_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_mkConst(v___x_1857_, v___x_1860_);
v___x_1862_ = l_Lean_mkApp4(v___x_1861_, v_p_1761_, v_e_x27_1843_, v_q_1764_, v_proof_1844_);
v___x_1863_ = 0;
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1862_);
lean_ctor_set(v___x_1846_, 0, v_a_1856_);
v___x_1865_ = v___x_1846_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1856_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1862_);
v___x_1865_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*2, v___x_1863_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1865_);
v___x_1867_ = v___x_1853_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
v___jp_1870_:
{
if (lean_obj_tag(v___y_1871_) == 0)
{
lean_object* v_a_1872_; 
v_a_1872_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___y_1871_);
v_a_1856_ = v_a_1872_;
goto v___jp_1855_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_del_object(v___x_1853_);
lean_dec(v_a_1851_);
lean_dec(v_a_1849_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_proof_1844_);
lean_dec_ref(v_e_x27_1843_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
v_a_1873_ = lean_ctor_get(v___y_1871_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___y_1871_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___y_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1849_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_proof_1844_);
lean_dec_ref(v_e_x27_1843_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v_a_1893_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1850_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1850_);
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
lean_del_object(v___x_1846_);
lean_dec_ref(v_proof_1844_);
lean_dec_ref(v_e_x27_1843_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v_a_1901_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1848_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1848_);
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
}
else
{
lean_object* v_e_x27_1910_; lean_object* v_proof_1911_; lean_object* v_e_x27_1912_; lean_object* v_proof_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1978_; 
v_e_x27_1910_ = lean_ctor_get(v_a_1763_, 0);
lean_inc_ref(v_e_x27_1910_);
v_proof_1911_ = lean_ctor_get(v_a_1763_, 1);
lean_inc_ref(v_proof_1911_);
lean_dec_ref(v_a_1763_);
v_e_x27_1912_ = lean_ctor_get(v_a_1842_, 0);
v_proof_1913_ = lean_ctor_get(v_a_1842_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1915_ = v_a_1842_;
v_isShared_1916_ = v_isSharedCheck_1978_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_proof_1913_);
lean_inc(v_e_x27_1912_);
lean_dec(v_a_1842_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1978_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; 
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc_ref(v_p_1761_);
v___x_1917_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1761_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
lean_inc(v_a_1759_);
lean_inc_ref(v_a_1758_);
lean_inc(v_a_1757_);
lean_inc_ref(v_a_1756_);
lean_inc_ref(v_q_1764_);
v___x_1919_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1764_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1961_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1961_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1961_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_a_1925_; lean_object* v___y_1940_; 
if (lean_obj_tag(v_e_1750_) == 7)
{
lean_object* v_binderName_1950_; lean_object* v_binderType_1951_; lean_object* v_body_1952_; uint8_t v_binderInfo_1953_; uint8_t v___y_1955_; uint8_t v___x_1957_; 
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
v_binderName_1950_ = lean_ctor_get(v_e_1750_, 0);
v_binderType_1951_ = lean_ctor_get(v_e_1750_, 1);
v_body_1952_ = lean_ctor_get(v_e_1750_, 2);
v_binderInfo_1953_ = lean_ctor_get_uint8(v_e_1750_, sizeof(void*)*3 + 8);
v___x_1957_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1951_, v_e_x27_1910_);
if (v___x_1957_ == 0)
{
v___y_1955_ = v___x_1957_;
goto v___jp_1954_;
}
else
{
uint8_t v___x_1958_; 
v___x_1958_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1952_, v_e_x27_1912_);
v___y_1955_ = v___x_1958_;
goto v___jp_1954_;
}
v___jp_1954_:
{
if (v___y_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_inc(v_binderName_1950_);
lean_dec_ref(v_e_1750_);
lean_inc_ref(v_e_x27_1912_);
lean_inc_ref(v_e_x27_1910_);
v___x_1956_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1950_, v_binderInfo_1953_, v_e_x27_1910_, v_e_x27_1912_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
v___y_1940_ = v___x_1956_;
goto v___jp_1939_;
}
else
{
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
v_a_1925_ = v_e_1750_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v_e_1750_);
v___x_1959_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__6, &l_Lean_Meta_Sym_Simp_simpArrow___closed__6_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__6);
v___x_1960_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1959_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
v___y_1940_ = v___x_1960_;
goto v___jp_1939_;
}
v___jp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1934_; 
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__10));
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1920_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_a_1918_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_mkConst(v___x_1926_, v___x_1929_);
v___x_1931_ = l_Lean_mkApp6(v___x_1930_, v_p_1761_, v_e_x27_1910_, v_q_1764_, v_e_x27_1912_, v_proof_1911_, v_proof_1913_);
v___x_1932_ = 0;
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1931_);
lean_ctor_set(v___x_1915_, 0, v_a_1925_);
v___x_1934_ = v___x_1915_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1931_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*2, v___x_1932_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1934_);
v___x_1936_ = v___x_1922_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
v___jp_1939_:
{
if (lean_obj_tag(v___y_1940_) == 0)
{
lean_object* v_a_1941_; 
v_a_1941_ = lean_ctor_get(v___y_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref(v___y_1940_);
v_a_1925_ = v_a_1941_;
goto v___jp_1924_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_del_object(v___x_1922_);
lean_dec(v_a_1920_);
lean_dec(v_a_1918_);
lean_del_object(v___x_1915_);
lean_dec_ref(v_proof_1913_);
lean_dec_ref(v_e_x27_1912_);
lean_dec_ref(v_proof_1911_);
lean_dec_ref(v_e_x27_1910_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
v_a_1942_ = lean_ctor_get(v___y_1940_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___y_1940_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___y_1940_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___y_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_a_1918_);
lean_del_object(v___x_1915_);
lean_dec_ref(v_proof_1913_);
lean_dec_ref(v_e_x27_1912_);
lean_dec_ref(v_proof_1911_);
lean_dec_ref(v_e_x27_1910_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v_a_1962_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1919_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1919_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_del_object(v___x_1915_);
lean_dec_ref(v_proof_1913_);
lean_dec_ref(v_e_x27_1912_);
lean_dec_ref(v_proof_1911_);
lean_dec_ref(v_e_x27_1910_);
lean_dec_ref(v_q_1764_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
v_a_1970_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1917_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1917_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_q_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
return v___x_1765_;
}
}
else
{
lean_dec_ref(v_p_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_e_1750_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow___boxed(lean_object* v_e_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Meta_Sym_Simp_simpArrow(v_e_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(lean_object* v_simpBody_1991_, lean_object* v_xs_1992_, lean_object* v_b_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_b_1993_);
v___x_2004_ = lean_apply_11(v_simpBody_1991_, v_b_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, lean_box(0));
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2093_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2093_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2093_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
if (lean_obj_tag(v_a_2005_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_xs_1992_);
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__0));
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2009_);
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
else
{
lean_object* v_e_x27_2013_; lean_object* v_proof_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2092_; 
lean_del_object(v___x_2007_);
v_e_x27_2013_ = lean_ctor_get(v_a_2005_, 0);
v_proof_2014_ = lean_ctor_get(v_a_2005_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2016_ = v_a_2005_;
v_isShared_2017_ = v_isSharedCheck_2092_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_proof_2014_);
lean_inc(v_e_x27_2013_);
lean_dec(v_a_2005_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2092_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
uint8_t v___x_2018_; uint8_t v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2018_ = 0;
v___x_2019_ = 1;
v___x_2020_ = 1;
v___x_2021_ = l_Lean_Meta_mkLambdaFVars(v_xs_1992_, v_proof_2014_, v___x_2018_, v___x_2019_, v___x_2018_, v___x_2019_, v___x_2020_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
lean_inc_ref(v_e_x27_2013_);
v___x_2023_ = l_Lean_Meta_mkForallFVars(v_xs_1992_, v_e_x27_2013_, v___x_2018_, v___x_2019_, v___x_2019_, v___x_2020_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2024_, v_a_1998_);
lean_dec(v_a_1998_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2025_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc_ref(v_xs_1992_);
v___x_2027_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_1992_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = l_Lean_Meta_mkLambdaFVars(v_xs_1992_, v_b_1993_, v___x_2018_, v___x_2019_, v___x_2018_, v___x_2019_, v___x_2020_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = l_Lean_Meta_mkLambdaFVars(v_xs_1992_, v_e_x27_2013_, v___x_2018_, v___x_2019_, v___x_2018_, v___x_2019_, v___x_2020_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec_ref(v_xs_1992_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2043_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2043_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2043_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = l_Lean_mkApp3(v_a_2028_, v_a_2030_, v_a_2032_, v_a_2022_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_2036_);
lean_ctor_set(v___x_2016_, 0, v_a_2026_);
v___x_2038_ = v___x_2016_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2026_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*2, v___x_2018_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_2030_);
lean_dec(v_a_2028_);
lean_dec(v_a_2026_);
lean_dec(v_a_2022_);
lean_del_object(v___x_2016_);
v_a_2044_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2031_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2031_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_a_2028_);
lean_dec(v_a_2026_);
lean_dec(v_a_2022_);
lean_del_object(v___x_2016_);
lean_dec_ref(v_e_x27_2013_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec_ref(v_xs_1992_);
v_a_2052_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2029_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2029_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2026_);
lean_dec(v_a_2022_);
lean_del_object(v___x_2016_);
lean_dec_ref(v_e_x27_2013_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_xs_1992_);
v_a_2060_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2027_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2027_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2022_);
lean_del_object(v___x_2016_);
lean_dec_ref(v_e_x27_2013_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_xs_1992_);
v_a_2068_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2025_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2025_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_a_2022_);
lean_del_object(v___x_2016_);
lean_dec_ref(v_e_x27_2013_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_xs_1992_);
v_a_2076_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2023_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2023_);
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
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_del_object(v___x_2016_);
lean_dec_ref(v_e_x27_2013_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_xs_1992_);
v_a_2084_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2021_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2021_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
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
}
}
}
else
{
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_xs_1992_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main___boxed(lean_object* v_simpBody_2094_, lean_object* v_xs_2095_, lean_object* v_b_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2094_, v_xs_2095_, v_b_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(lean_object* v_e_2108_, lean_object* v_n_2109_){
_start:
{
if (lean_obj_tag(v_e_2108_) == 7)
{
lean_object* v_body_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_body_2110_ = lean_ctor_get(v_e_2108_, 2);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_expr_has_loose_bvar(v_body_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
return v_n_2109_;
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_add(v_n_2109_, v___x_2113_);
lean_dec(v_n_2109_);
v_e_2108_ = v_body_2110_;
v_n_2109_ = v___x_2114_;
goto _start;
}
}
else
{
return v_n_2109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize___boxed(lean_object* v_e_2116_, lean_object* v_n_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v_e_2116_, v_n_2117_);
lean_dec_ref(v_e_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(lean_object* v_k_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v_b_2125_, lean_object* v_c_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_apply_12(v_k_2119_, v_b_2125_, v_c_2126_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, lean_box(0));
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v_b_2139_, lean_object* v_c_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(v_k_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v_b_2139_, v_c_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(lean_object* v_type_2147_, lean_object* v_maxFVars_x3f_2148_, lean_object* v_k_2149_, uint8_t v_cleanupAnnotations_2150_, uint8_t v_whnfType_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___f_2162_; lean_object* v___x_2163_; 
v___f_2162_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2162_, 0, v_k_2149_);
lean_closure_set(v___f_2162_, 1, v___y_2152_);
lean_closure_set(v___f_2162_, 2, v___y_2153_);
lean_closure_set(v___f_2162_, 3, v___y_2154_);
lean_closure_set(v___f_2162_, 4, v___y_2155_);
lean_closure_set(v___f_2162_, 5, v___y_2156_);
v___x_2163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2147_, v_maxFVars_x3f_2148_, v___f_2162_, v_cleanupAnnotations_2150_, v_whnfType_2151_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2163_) == 0)
{
return v___x_2163_;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___boxed(lean_object* v_type_2172_, lean_object* v_maxFVars_x3f_2173_, lean_object* v_k_2174_, lean_object* v_cleanupAnnotations_2175_, lean_object* v_whnfType_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2187_; uint8_t v_whnfType_boxed_2188_; lean_object* v_res_2189_; 
v_cleanupAnnotations_boxed_2187_ = lean_unbox(v_cleanupAnnotations_2175_);
v_whnfType_boxed_2188_ = lean_unbox(v_whnfType_2176_);
v_res_2189_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2172_, v_maxFVars_x3f_2173_, v_k_2174_, v_cleanupAnnotations_boxed_2187_, v_whnfType_boxed_2188_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(lean_object* v_00_u03b1_2190_, lean_object* v_type_2191_, lean_object* v_maxFVars_x3f_2192_, lean_object* v_k_2193_, uint8_t v_cleanupAnnotations_2194_, uint8_t v_whnfType_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2191_, v_maxFVars_x3f_2192_, v_k_2193_, v_cleanupAnnotations_2194_, v_whnfType_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_type_2208_, lean_object* v_maxFVars_x3f_2209_, lean_object* v_k_2210_, lean_object* v_cleanupAnnotations_2211_, lean_object* v_whnfType_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2223_; uint8_t v_whnfType_boxed_2224_; lean_object* v_res_2225_; 
v_cleanupAnnotations_boxed_2223_ = lean_unbox(v_cleanupAnnotations_2211_);
v_whnfType_boxed_2224_ = lean_unbox(v_whnfType_2212_);
v_res_2225_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(v_00_u03b1_2207_, v_type_2208_, v_maxFVars_x3f_2209_, v_k_2210_, v_cleanupAnnotations_boxed_2223_, v_whnfType_boxed_2224_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(lean_object* v___y_2226_, lean_object* v_cache_2227_, lean_object* v_funext_2228_, lean_object* v_a_x3f_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v_numSteps_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2242_; 
v___x_2231_ = lean_st_ref_take(v___y_2226_);
v_numSteps_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; 
v_unused_2243_ = lean_ctor_get(v___x_2231_, 2);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v___x_2231_, 1);
lean_dec(v_unused_2244_);
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2242_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_numSteps_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2242_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 2, v_funext_2228_);
lean_ctor_set(v___x_2234_, 1, v_cache_2227_);
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_numSteps_2232_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_cache_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_funext_2228_);
v___x_2237_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_st_ref_set(v___y_2226_, v___x_2237_);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0___boxed(lean_object* v___y_2245_, lean_object* v_cache_2246_, lean_object* v_funext_2247_, lean_object* v_a_x3f_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2245_, v_cache_2246_, v_funext_2247_, v_a_x3f_2248_);
lean_dec(v_a_x3f_2248_);
lean_dec(v___y_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(lean_object* v_simpBody_2251_, lean_object* v_xs_2252_, lean_object* v_b_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v_wellBehavedMethods_2264_; 
v_wellBehavedMethods_2264_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*2);
if (v_wellBehavedMethods_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_cache_2267_; lean_object* v_funext_2268_; lean_object* v_a_2270_; lean_object* v___x_2281_; 
v___x_2265_ = lean_st_ref_get(v___y_2256_);
v___x_2266_ = lean_st_ref_get(v___y_2256_);
v_cache_2267_ = lean_ctor_get(v___x_2265_, 1);
lean_inc_ref(v_cache_2267_);
lean_dec(v___x_2265_);
v_funext_2268_ = lean_ctor_get(v___x_2266_, 2);
lean_inc_ref(v_funext_2268_);
lean_dec(v___x_2266_);
v___x_2281_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_2253_, v___y_2258_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2281_);
lean_inc(v___y_2256_);
v___x_2283_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2251_, v_xs_2252_, v_a_2282_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2300_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2300_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2300_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
lean_inc(v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 1);
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v___x_2290_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2256_, v_cache_2267_, v_funext_2268_, v___x_2289_);
lean_dec_ref(v___x_2289_);
lean_dec(v___y_2256_);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; 
v_unused_2298_ = lean_ctor_get(v___x_2290_, 0);
lean_dec(v_unused_2298_);
v___x_2292_ = v___x_2290_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v___x_2290_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v_a_2284_);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2284_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
else
{
lean_object* v_a_2301_; 
v_a_2301_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2283_);
v_a_2270_ = v_a_2301_;
goto v___jp_2269_;
}
}
else
{
lean_object* v_a_2302_; 
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v_xs_2252_);
lean_dec_ref(v_simpBody_2251_);
v_a_2302_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2302_);
lean_dec_ref(v___x_2281_);
v_a_2270_ = v_a_2302_;
goto v___jp_2269_;
}
v___jp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2256_, v_cache_2267_, v_funext_2268_, v___x_2271_);
lean_dec(v___y_2256_);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v___x_2272_, 0);
lean_dec(v_unused_2280_);
v___x_2274_ = v___x_2272_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v___x_2272_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 1);
lean_ctor_set(v___x_2274_, 0, v_a_2270_);
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2270_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_2253_, v___y_2258_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2251_, v_xs_2252_, v_a_2304_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2305_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v_xs_2252_);
lean_dec_ref(v_simpBody_2251_);
v_a_2306_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2303_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2303_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed(lean_object* v_simpBody_2314_, lean_object* v_xs_2315_, lean_object* v_b_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(v_simpBody_2314_, v_xs_2315_, v_b_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object* v_simpArrow_2328_, lean_object* v_simpBody_2329_, lean_object* v_e_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Lean_Expr_isArrow(v_e_2330_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_dec_ref(v_simpArrow_2328_);
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
lean_inc_ref(v_a_2336_);
lean_inc_ref(v_e_2330_);
v___x_2342_ = l_Lean_Meta_isProp(v_e_2330_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2359_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2359_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2359_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_unbox(v_a_2343_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2351_; 
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_e_2330_);
lean_dec_ref(v_simpBody_2329_);
v___x_2348_ = lean_alloc_ctor(0, 0, 1);
v___x_2349_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
lean_ctor_set_uint8(v___x_2348_, 0, v___x_2349_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2348_);
v___x_2351_ = v___x_2345_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2348_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
else
{
lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_del_object(v___x_2345_);
lean_dec(v_a_2343_);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed), 13, 1);
lean_closure_set(v___f_2353_, 0, v_simpBody_2329_);
v___x_2354_ = l_Lean_Expr_bindingBody_x21(v_e_2330_);
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v___x_2354_, v___x_2355_);
lean_dec_ref(v___x_2354_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
v___x_2358_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_e_2330_, v___x_2357_, v___f_2353_, v___x_2341_, v___x_2341_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_e_2330_);
lean_dec_ref(v_simpBody_2329_);
v_a_2360_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2342_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2342_);
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
lean_object* v___x_2368_; 
lean_dec_ref(v_simpBody_2329_);
v___x_2368_ = lean_apply_11(v_simpArrow_2328_, v_e_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, lean_box(0));
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object* v_simpArrow_2369_, lean_object* v_simpBody_2370_, lean_object* v_e_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v_simpArrow_2369_, v_simpBody_2370_, v_e_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object* v_e_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__0));
v___x_2397_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__1));
v___x_2398_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v___x_2396_, v___x_2397_, v_e_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object* v_e_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v_res_2410_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Forall(builtin);
}
#ifdef __cplusplus
}
#endif
