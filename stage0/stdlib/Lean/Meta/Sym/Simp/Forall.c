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
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_true_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 244, 117, 192, 201, 44, 53, 165)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrow_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 60, 249, 93, 169, 23, 87, 100)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "arrow_congr_right"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 119, 110, 93, 174, 252, 11, 102)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 72, 118, 56, 86, 132, 84, 122)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value),LEAN_SCALAR_PTR_LITERAL(166, 43, 230, 22, 134, 52, 48, 206)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "true_arrow"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value),LEAN_SCALAR_PTR_LITERAL(167, 3, 129, 158, 41, 225, 71, 211)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "true_arrow_congr_right"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value),LEAN_SCALAR_PTR_LITERAL(118, 96, 91, 171, 163, 176, 69, 89)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "true_arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value),LEAN_SCALAR_PTR_LITERAL(6, 117, 111, 18, 228, 157, 82, 38)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "true_arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value),LEAN_SCALAR_PTR_LITERAL(229, 237, 254, 33, 163, 119, 59, 188)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21;
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
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "implies_congr_right"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 214, 41, 106, 32, 244, 82, 54)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallS!"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__5;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implies_congr_left"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 33, 3, 245, 8, 162, 217, 112)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrow___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value;
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
lean_inc_ref_n(v_a_15_, 4);
lean_inc(v___x_14_);
v___x_47_ = l_Lean_mkLambda(v___x_14_, v___x_44_, v_a_15_, v___x_46_);
lean_inc(v___x_16_);
v___x_48_ = l_Lean_Expr_bvar___override(v___x_16_);
lean_inc_ref_n(v_a_17_, 2);
v___x_49_ = l_Lean_mkAppB(v_a_17_, v___x_48_, v___x_45_);
v___x_50_ = l_Lean_mkLambda(v___x_18_, v___x_44_, v___x_49_, v___x_46_);
v___x_51_ = l_Lean_mkLambda(v___x_19_, v___x_44_, v_a_15_, v___x_50_);
v___x_52_ = l_Lean_mkLambda(v___x_14_, v___x_44_, v_a_15_, v___x_51_);
lean_inc_ref(v_p_x27_34_);
lean_inc_ref(v_prop_20_);
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
lean_inc_ref_n(v_a_15_, 2);
lean_inc_ref(v___x_69_);
v___x_70_ = l_Lean_mkApp3(v___x_69_, v_a_15_, v_a_17_, v_p_25_);
lean_inc_ref_n(v_q_26_, 2);
v___x_71_ = l_Lean_mkApp3(v___x_69_, v_a_15_, v_a_17_, v_q_26_);
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
uint8_t v___x_2437__boxed_126_; uint8_t v___x_2438__boxed_127_; uint8_t v___x_2439__boxed_128_; lean_object* v_res_129_; 
v___x_2437__boxed_126_ = lean_unbox(v___x_107_);
v___x_2438__boxed_127_ = lean_unbox(v___x_108_);
v___x_2439__boxed_128_ = lean_unbox(v___x_109_);
v_res_129_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(v___x_95_, v_a_96_, v___x_97_, v___x_98_, v_xs_99_, v___x_100_, v_a_101_, v___x_102_, v_a_103_, v___x_104_, v___x_105_, v_prop_106_, v___x_2437__boxed_126_, v___x_2438__boxed_127_, v___x_2439__boxed_128_, v___x_110_, v_p_111_, v_q_112_, v_h_113_, v___x_114_, v___x_115_, v___x_116_, v___x_117_, v___x_118_, v___x_119_, v_p_x27_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
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
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_137_ = lean_apply_6(v_k_130_, v_b_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_138_, lean_object* v_b_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(v_k_138_, v_b_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
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
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
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
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
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
lean_inc_n(v_a_248_, 2);
lean_dec_ref(v___x_247_);
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0));
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1));
lean_inc(v_a_220_);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_220_);
lean_ctor_set(v___x_251_, 1, v___x_221_);
lean_inc_ref(v___x_251_);
v___x_252_ = l_Lean_mkConst(v___x_250_, v___x_251_);
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
uint8_t v___x_2726__boxed_288_; uint8_t v___x_2727__boxed_289_; uint8_t v___x_2728__boxed_290_; lean_object* v_res_291_; 
v___x_2726__boxed_288_ = lean_unbox(v___x_262_);
v___x_2727__boxed_289_ = lean_unbox(v___x_263_);
v___x_2728__boxed_290_ = lean_unbox(v___x_264_);
v_res_291_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(v_xs_260_, v___x_261_, v___x_2726__boxed_288_, v___x_2727__boxed_289_, v___x_2728__boxed_290_, v_p_265_, v_q_266_, v_a_267_, v___x_268_, v_a_269_, v___x_270_, v___x_271_, v___x_272_, v___x_273_, v___x_274_, v___x_275_, v_prop_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, v___x_281_, v_h_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
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
uint8_t v___x_2868__boxed_358_; uint8_t v___x_2869__boxed_359_; uint8_t v___x_2870__boxed_360_; lean_object* v_res_361_; 
v___x_2868__boxed_358_ = lean_unbox(v___x_343_);
v___x_2869__boxed_359_ = lean_unbox(v___x_344_);
v___x_2870__boxed_360_ = lean_unbox(v___x_345_);
v_res_361_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(v_p_340_, v_xs_341_, v_prop_342_, v___x_2868__boxed_358_, v___x_2869__boxed_359_, v___x_2870__boxed_360_, v_a_346_, v_a_347_, v___x_348_, v___x_349_, v___x_350_, v___x_351_, v_q_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
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
uint8_t v___x_2963__boxed_403_; uint8_t v___x_2964__boxed_404_; uint8_t v___x_2965__boxed_405_; lean_object* v_res_406_; 
v___x_2963__boxed_403_ = lean_unbox(v___x_389_);
v___x_2964__boxed_404_ = lean_unbox(v___x_390_);
v___x_2965__boxed_405_ = lean_unbox(v___x_391_);
v_res_406_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(v_xs_387_, v_prop_388_, v___x_2963__boxed_403_, v___x_2964__boxed_404_, v___x_2965__boxed_405_, v_a_392_, v_a_393_, v___x_394_, v___x_395_, v___x_396_, v_p_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
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
lean_inc_n(v_a_427_, 2);
lean_dec_ref(v___x_426_);
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
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
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
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
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
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
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
v_debug_542_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*10);
lean_dec(v___x_541_);
if (v_debug_542_ == 0)
{
v___y_538_ = v___y_531_;
goto v___jp_537_;
}
else
{
lean_object* v___x_543_; 
lean_inc_ref(v_f_528_);
v___x_543_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; 
lean_dec_ref(v___x_543_);
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
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1___boxed(lean_object* v_f_561_, lean_object* v_a_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_561_, v_a_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(lean_object* v_f_571_, lean_object* v_a_u2081_572_, lean_object* v_a_u2082_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
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
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
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
lean_inc_ref(v_binderType_634_);
v___x_646_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_634_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_n(v_a_647_, 2);
lean_dec_ref(v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_649_ = lean_box(0);
lean_inc(v_v_642_);
v___x_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_650_, 0, v_v_642_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
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
return v___x_638_;
}
}
else
{
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
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(lean_object* v_x_703_, uint8_t v_bi_704_, lean_object* v_t_705_, lean_object* v_b_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___y_715_; lean_object* v___x_718_; uint8_t v_debug_719_; 
v___x_718_ = lean_st_ref_get(v___y_708_);
v_debug_719_ = lean_ctor_get_uint8(v___x_718_, sizeof(void*)*10);
lean_dec(v___x_718_);
if (v_debug_719_ == 0)
{
v___y_715_ = v___y_708_;
goto v___jp_714_;
}
else
{
lean_object* v___x_720_; 
lean_inc_ref(v_t_705_);
v___x_720_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_721_; 
lean_dec_ref(v___x_720_);
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
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
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
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_e_751_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; 
lean_dec_ref(v_e_751_);
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
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v___x_779_; 
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
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_789_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(lean_object* v_head_790_, lean_object* v_00___791_){
_start:
{
lean_object* v_v_792_; uint8_t v___x_793_; 
v_v_792_ = lean_ctor_get(v_head_790_, 2);
v___x_793_ = l_Lean_Level_isZero(v_v_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0___boxed(lean_object* v_head_794_, lean_object* v_00___795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_794_, v_00___795_);
lean_dec_ref(v_head_794_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(lean_object* v_f_798_, lean_object* v_a_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___y_808_; lean_object* v___x_811_; uint8_t v_debug_812_; 
v___x_811_ = lean_st_ref_get(v___y_801_);
v_debug_812_ = lean_ctor_get_uint8(v___x_811_, sizeof(void*)*10);
lean_dec(v___x_811_);
if (v_debug_812_ == 0)
{
v___y_808_ = v___y_801_;
goto v___jp_807_;
}
else
{
lean_object* v___x_813_; 
lean_inc_ref(v_f_798_);
v___x_813_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_798_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_814_; 
lean_dec_ref(v___x_813_);
lean_inc_ref(v_a_799_);
v___x_814_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref(v___x_814_);
v___y_808_ = v___y_801_;
goto v___jp_807_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_a_799_);
lean_dec_ref(v_f_798_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
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
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_a_799_);
lean_dec_ref(v_f_798_);
v_a_823_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_813_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
v___jp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Lean_Expr_app___override(v_f_798_, v_a_799_);
v___x_810_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_809_, v___y_808_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(lean_object* v_f_831_, lean_object* v_a_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_831_, v_a_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(lean_object* v_f_841_, lean_object* v_a_u2081_842_, lean_object* v_a_u2082_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_841_, v_a_u2081_842_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
v___x_856_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_a_855_, v_a_u2082_843_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_856_;
}
else
{
lean_dec_ref(v_a_u2082_843_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(lean_object* v_f_857_, lean_object* v_a_u2081_858_, lean_object* v_a_u2082_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v_f_857_, v_a_u2081_858_, v_a_u2082_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
return v_res_870_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11));
v___x_897_ = l_Lean_mkConst(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_box(0);
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14));
v___x_904_ = l_Lean_mkConst(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(0);
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17));
v___x_911_ = l_Lean_mkConst(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_box(0);
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20));
v___x_918_ = l_Lean_mkConst(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_box(0);
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23));
v___x_925_ = l_Lean_mkConst(v___x_924_, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_box(0);
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26));
v___x_932_ = l_Lean_mkConst(v___x_931_, v___x_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(lean_object* v_e_933_, lean_object* v_infos_934_, lean_object* v_simpBody_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_975_; uint8_t v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; uint8_t v___y_984_; 
if (lean_obj_tag(v_infos_934_) == 0)
{
lean_object* v___x_988_; 
lean_inc(v_a_944_);
lean_inc_ref(v_a_943_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
v___x_988_ = lean_apply_11(v_simpBody_935_, v_e_933_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, lean_box(0));
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_a_989_);
lean_ctor_set(v___x_993_, 1, v_infos_934_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_988_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_988_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_head_1006_; lean_object* v_tail_1007_; uint8_t v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; uint8_t v___y_1013_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_head_1006_ = lean_ctor_get(v_infos_934_, 0);
v_tail_1007_ = lean_ctor_get(v_infos_934_, 1);
lean_inc_ref(v_e_933_);
v___x_1018_ = l_Lean_Expr_cleanupAnnotations(v_e_933_);
v___x_1019_ = l_Lean_Expr_isApp(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec_ref(v___x_1018_);
v___y_947_ = v_a_936_;
v___y_948_ = v_a_937_;
v___y_949_ = v_a_938_;
v___y_950_ = v_a_939_;
v___y_951_ = v_a_940_;
v___y_952_ = v_a_941_;
v___y_953_ = v_a_942_;
v___y_954_ = v_a_943_;
v___y_955_ = v_a_944_;
goto v___jp_946_;
}
else
{
lean_object* v_arg_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_arg_1020_ = lean_ctor_get(v___x_1018_, 1);
lean_inc_ref(v_arg_1020_);
v___x_1021_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1018_);
v___x_1022_ = l_Lean_Expr_isApp(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v___x_1021_);
lean_dec_ref(v_arg_1020_);
v___y_947_ = v_a_936_;
v___y_948_ = v_a_937_;
v___y_949_ = v_a_938_;
v___y_950_ = v_a_939_;
v___y_951_ = v_a_940_;
v___y_952_ = v_a_941_;
v___y_953_ = v_a_942_;
v___y_954_ = v_a_943_;
v___y_955_ = v_a_944_;
goto v___jp_946_;
}
else
{
lean_object* v_arg_1023_; lean_object* v___x_1024_; lean_object* v_proof_1026_; uint8_t v___y_1027_; uint8_t v___y_1028_; uint8_t v___y_1055_; uint8_t v___y_1056_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; uint8_t v___y_1087_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; uint8_t v___y_1117_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___y_1145_; uint8_t v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1158_; lean_object* v___y_1159_; uint8_t v___y_1160_; 
v_arg_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc_ref(v_arg_1023_);
v___x_1024_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1021_);
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_1143_ = l_Lean_Expr_isConstOf(v___x_1024_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
v___y_947_ = v_a_936_;
v___y_948_ = v_a_937_;
v___y_949_ = v_a_938_;
v___y_950_ = v_a_939_;
v___y_951_ = v_a_940_;
v___y_952_ = v_a_941_;
v___y_953_ = v_a_942_;
v___y_954_ = v_a_943_;
v___y_955_ = v_a_944_;
goto v___jp_946_;
}
else
{
lean_object* v___x_1175_; 
lean_dec_ref(v_e_933_);
lean_inc(v_a_944_);
lean_inc_ref(v_a_943_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_arg_1023_);
v___x_1175_ = lean_sym_simp(v_arg_1023_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1023_, v_a_1176_);
v___x_1178_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v___x_1177_, v_a_939_);
lean_dec_ref(v___x_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; uint8_t v___y_1181_; lean_object* v___y_1182_; uint8_t v___y_1183_; uint8_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; uint8_t v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; uint8_t v___y_1252_; uint8_t v___y_1279_; uint8_t v___x_1342_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1178_);
v___x_1342_ = lean_unbox(v_a_1179_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_unbox(v_a_1179_);
lean_dec(v_a_1179_);
v___y_1279_ = v___x_1343_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_dec(v_a_1179_);
v___x_1344_ = lean_box(0);
v___x_1345_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1344_);
if (v___x_1345_ == 0)
{
v___y_1279_ = v___x_1345_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_simpBody_935_);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_infos_934_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1410_ = lean_ctor_get(v_infos_934_, 1);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_infos_934_, 0);
lean_dec(v_unused_1411_);
v___x_1347_ = v_infos_934_;
v_isShared_1348_ = v_isSharedCheck_1409_;
goto v_resetjp_1346_;
}
else
{
lean_dec(v_infos_934_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1409_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
if (lean_obj_tag(v_a_1176_) == 0)
{
uint8_t v_contextDependent_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_arg_1023_);
v_contextDependent_1349_ = lean_ctor_get_uint8(v_a_1176_, 1);
lean_dec_ref(v_a_1176_);
v___x_1350_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_939_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1366_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1366_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1366_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24);
v___x_1357_ = l_Lean_Expr_app___override(v___x_1356_, v_arg_1020_);
v___x_1358_ = 0;
v___x_1359_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1359_, 0, v_a_1351_);
lean_ctor_set(v___x_1359_, 1, v___x_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*2, v___x_1358_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*2 + 1, v_contextDependent_1349_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
lean_ctor_set(v___x_1347_, 1, v___x_1355_);
lean_ctor_set(v___x_1347_, 0, v___x_1359_);
v___x_1361_ = v___x_1347_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1355_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1361_);
v___x_1363_ = v___x_1353_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_del_object(v___x_1347_);
lean_dec_ref(v_arg_1020_);
v_a_1367_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1350_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1350_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v_proof_1375_; uint8_t v_contextDependent_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1407_; 
v_proof_1375_ = lean_ctor_get(v_a_1176_, 1);
v_contextDependent_1376_ = lean_ctor_get_uint8(v_a_1176_, sizeof(void*)*2 + 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_a_1176_, 0);
lean_dec(v_unused_1408_);
v___x_1378_ = v_a_1176_;
v_isShared_1379_ = v_isSharedCheck_1407_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_proof_1375_);
lean_dec(v_a_1176_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1407_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_939_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1398_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1398_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1398_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1390_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27);
v___x_1387_ = l_Lean_mkApp3(v___x_1386_, v_arg_1023_, v_arg_1020_, v_proof_1375_);
v___x_1388_ = 0;
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v___x_1387_);
lean_ctor_set(v___x_1378_, 0, v_a_1381_);
v___x_1390_ = v___x_1378_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1381_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*2 + 1, v_contextDependent_1376_);
v___x_1390_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
lean_ctor_set_uint8(v___x_1390_, sizeof(void*)*2, v___x_1388_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
lean_ctor_set(v___x_1347_, 1, v___x_1385_);
lean_ctor_set(v___x_1347_, 0, v___x_1390_);
v___x_1392_ = v___x_1347_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1385_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1392_);
v___x_1394_ = v___x_1383_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_del_object(v___x_1378_);
lean_dec_ref(v_proof_1375_);
lean_del_object(v___x_1347_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
v_a_1399_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1380_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1380_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
}
}
v___jp_1180_:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1023_, v_a_939_);
lean_dec_ref(v_arg_1023_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1207_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1207_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1207_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_unbox(v_a_1185_);
lean_dec(v_a_1185_);
if (v___x_1189_ == 0)
{
lean_del_object(v___x_1187_);
lean_dec(v___y_1182_);
lean_dec_ref(v_arg_1020_);
v___y_975_ = v___y_1183_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_del_object(v___x_1187_);
lean_dec(v___y_1182_);
lean_dec_ref(v_arg_1020_);
v___y_975_ = v___y_1183_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1204_; 
v_isSharedCheck_1204_ = !lean_is_exclusive(v_infos_934_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; lean_object* v_unused_1206_; 
v_unused_1205_ = lean_ctor_get(v_infos_934_, 1);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_infos_934_, 0);
lean_dec(v_unused_1206_);
v___x_1193_ = v_infos_934_;
v_isShared_1194_ = v_isSharedCheck_1204_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v_infos_934_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1204_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12);
lean_inc_ref(v_arg_1020_);
v___x_1196_ = l_Lean_Expr_app___override(v___x_1195_, v_arg_1020_);
v___x_1197_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1197_, 0, v_arg_1020_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*2, v___y_1181_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*2 + 1, v___y_1183_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 0);
lean_ctor_set(v___x_1193_, 1, v___y_1182_);
lean_ctor_set(v___x_1193_, 0, v___x_1197_);
v___x_1199_ = v___x_1193_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___y_1182_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1199_);
v___x_1201_ = v___x_1187_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
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
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v___y_1182_);
lean_dec_ref(v_arg_1020_);
lean_dec_ref(v_infos_934_);
v_a_1208_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1184_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1184_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
v___jp_1216_:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1023_, v_a_939_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1238_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1238_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1238_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_unbox(v_a_1223_);
if (v___x_1227_ == 0)
{
uint8_t v___x_1228_; 
lean_del_object(v___x_1225_);
v___x_1228_ = lean_unbox(v_a_1223_);
lean_dec(v_a_1223_);
v___y_1083_ = v___y_1218_;
v___y_1084_ = v___y_1221_;
v___y_1085_ = v___y_1219_;
v___y_1086_ = v___y_1220_;
v___y_1087_ = v___x_1228_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
lean_dec(v_a_1223_);
v___x_1229_ = lean_box(0);
v___x_1230_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_del_object(v___x_1225_);
v___y_1083_ = v___y_1218_;
v___y_1084_ = v___y_1221_;
v___y_1085_ = v___y_1219_;
v___y_1086_ = v___y_1220_;
v___y_1087_ = v___x_1230_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec(v_head_1006_);
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15);
lean_inc_ref(v___y_1219_);
v___x_1232_ = l_Lean_mkApp3(v___x_1231_, v_arg_1020_, v___y_1219_, v___y_1218_);
v___x_1233_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1233_, 0, v___y_1219_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*2, v___y_1217_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*2 + 1, v___y_1221_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___y_1220_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1234_);
v___x_1236_ = v___x_1225_;
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
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1239_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1222_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1222_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
v___jp_1247_:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___y_1249_, v_a_939_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1269_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1269_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1269_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_unbox(v_a_1254_);
if (v___x_1258_ == 0)
{
uint8_t v___x_1259_; 
lean_del_object(v___x_1256_);
v___x_1259_ = lean_unbox(v_a_1254_);
lean_dec(v_a_1254_);
v___y_1113_ = v___y_1252_;
v___y_1114_ = v___y_1249_;
v___y_1115_ = v___y_1250_;
v___y_1116_ = v___y_1251_;
v___y_1117_ = v___x_1259_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
lean_dec(v_a_1254_);
v___x_1260_ = lean_box(0);
v___x_1261_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_del_object(v___x_1256_);
v___y_1113_ = v___y_1252_;
v___y_1114_ = v___y_1249_;
v___y_1115_ = v___y_1250_;
v___y_1116_ = v___y_1251_;
v___y_1117_ = v___x_1261_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___x_1024_);
lean_dec(v_head_1006_);
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18);
lean_inc_ref(v_arg_1020_);
v___x_1263_ = l_Lean_mkApp3(v___x_1262_, v_arg_1023_, v_arg_1020_, v___y_1250_);
v___x_1264_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1264_, 0, v_arg_1020_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*2, v___y_1248_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*2 + 1, v___y_1252_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___y_1251_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1265_);
v___x_1267_ = v___x_1256_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1270_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1253_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1253_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
v___jp_1278_:
{
lean_object* v___x_1280_; 
lean_inc(v_tail_1007_);
lean_inc_ref(v_arg_1020_);
v___x_1280_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arg_1020_, v_tail_1007_, v_simpBody_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v_fst_1282_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_fst_1282_);
v_snd_1283_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_snd_1283_);
lean_dec(v_a_1281_);
v___x_1284_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1020_, v_fst_1282_);
v___x_1285_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___x_1284_, v_a_939_);
lean_dec_ref(v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; uint8_t v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = lean_unbox(v_a_1286_);
if (v___x_1287_ == 0)
{
if (lean_obj_tag(v_a_1176_) == 0)
{
if (lean_obj_tag(v_fst_1282_) == 0)
{
uint8_t v_contextDependent_1288_; 
lean_dec_ref(v___x_1024_);
v_contextDependent_1288_ = lean_ctor_get_uint8(v_a_1176_, 1);
lean_dec_ref(v_a_1176_);
if (v_contextDependent_1288_ == 0)
{
uint8_t v_contextDependent_1289_; uint8_t v___x_1290_; 
v_contextDependent_1289_ = lean_ctor_get_uint8(v_fst_1282_, 1);
lean_dec_ref(v_fst_1282_);
v___x_1290_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1181_ = v___x_1290_;
v___y_1182_ = v_snd_1283_;
v___y_1183_ = v_contextDependent_1289_;
goto v___jp_1180_;
}
else
{
uint8_t v___x_1291_; 
lean_dec_ref(v_fst_1282_);
v___x_1291_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1181_ = v___x_1291_;
v___y_1182_ = v_snd_1283_;
v___y_1183_ = v___x_1143_;
goto v___jp_1180_;
}
}
else
{
uint8_t v_contextDependent_1292_; 
lean_inc(v_head_1006_);
lean_dec_ref(v_infos_934_);
v_contextDependent_1292_ = lean_ctor_get_uint8(v_a_1176_, 1);
lean_dec_ref(v_a_1176_);
if (v_contextDependent_1292_ == 0)
{
lean_object* v_e_x27_1293_; lean_object* v_proof_1294_; uint8_t v_contextDependent_1295_; uint8_t v___x_1296_; 
v_e_x27_1293_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc_ref(v_e_x27_1293_);
v_proof_1294_ = lean_ctor_get(v_fst_1282_, 1);
lean_inc_ref(v_proof_1294_);
v_contextDependent_1295_ = lean_ctor_get_uint8(v_fst_1282_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_1282_);
v___x_1296_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1217_ = v___x_1296_;
v___y_1218_ = v_proof_1294_;
v___y_1219_ = v_e_x27_1293_;
v___y_1220_ = v_snd_1283_;
v___y_1221_ = v_contextDependent_1295_;
goto v___jp_1216_;
}
else
{
lean_object* v_e_x27_1297_; lean_object* v_proof_1298_; uint8_t v___x_1299_; 
v_e_x27_1297_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc_ref(v_e_x27_1297_);
v_proof_1298_ = lean_ctor_get(v_fst_1282_, 1);
lean_inc_ref(v_proof_1298_);
lean_dec_ref(v_fst_1282_);
v___x_1299_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1217_ = v___x_1299_;
v___y_1218_ = v_proof_1298_;
v___y_1219_ = v_e_x27_1297_;
v___y_1220_ = v_snd_1283_;
v___y_1221_ = v___x_1143_;
goto v___jp_1216_;
}
}
}
else
{
lean_inc(v_head_1006_);
lean_dec_ref(v_infos_934_);
if (lean_obj_tag(v_fst_1282_) == 0)
{
uint8_t v_contextDependent_1300_; 
v_contextDependent_1300_ = lean_ctor_get_uint8(v_a_1176_, sizeof(void*)*2 + 1);
if (v_contextDependent_1300_ == 0)
{
lean_object* v_e_x27_1301_; lean_object* v_proof_1302_; uint8_t v_contextDependent_1303_; uint8_t v___x_1304_; 
v_e_x27_1301_ = lean_ctor_get(v_a_1176_, 0);
lean_inc_ref(v_e_x27_1301_);
v_proof_1302_ = lean_ctor_get(v_a_1176_, 1);
lean_inc_ref(v_proof_1302_);
lean_dec_ref(v_a_1176_);
v_contextDependent_1303_ = lean_ctor_get_uint8(v_fst_1282_, 1);
lean_dec_ref(v_fst_1282_);
v___x_1304_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1248_ = v___x_1304_;
v___y_1249_ = v_e_x27_1301_;
v___y_1250_ = v_proof_1302_;
v___y_1251_ = v_snd_1283_;
v___y_1252_ = v_contextDependent_1303_;
goto v___jp_1247_;
}
else
{
lean_object* v_e_x27_1305_; lean_object* v_proof_1306_; uint8_t v___x_1307_; 
lean_dec_ref(v_fst_1282_);
v_e_x27_1305_ = lean_ctor_get(v_a_1176_, 0);
lean_inc_ref(v_e_x27_1305_);
v_proof_1306_ = lean_ctor_get(v_a_1176_, 1);
lean_inc_ref(v_proof_1306_);
lean_dec_ref(v_a_1176_);
v___x_1307_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1248_ = v___x_1307_;
v___y_1249_ = v_e_x27_1305_;
v___y_1250_ = v_proof_1306_;
v___y_1251_ = v_snd_1283_;
v___y_1252_ = v___x_1143_;
goto v___jp_1247_;
}
}
else
{
lean_object* v_e_x27_1308_; lean_object* v_proof_1309_; uint8_t v_contextDependent_1310_; lean_object* v_e_x27_1311_; lean_object* v_proof_1312_; uint8_t v_contextDependent_1313_; lean_object* v___x_1314_; 
v_e_x27_1308_ = lean_ctor_get(v_a_1176_, 0);
lean_inc_ref(v_e_x27_1308_);
v_proof_1309_ = lean_ctor_get(v_a_1176_, 1);
lean_inc_ref(v_proof_1309_);
v_contextDependent_1310_ = lean_ctor_get_uint8(v_a_1176_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1176_);
v_e_x27_1311_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc_ref(v_e_x27_1311_);
v_proof_1312_ = lean_ctor_get(v_fst_1282_, 1);
lean_inc_ref(v_proof_1312_);
v_contextDependent_1313_ = lean_ctor_get_uint8(v_fst_1282_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_1282_);
v___x_1314_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1308_, v_a_939_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = lean_unbox(v_a_1315_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; 
lean_dec(v_a_1286_);
v___x_1317_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
v___y_1153_ = v_contextDependent_1310_;
v___y_1154_ = v_proof_1312_;
v___y_1155_ = v_e_x27_1308_;
v___y_1156_ = v_proof_1309_;
v___y_1157_ = v_snd_1283_;
v___y_1158_ = v_contextDependent_1313_;
v___y_1159_ = v_e_x27_1311_;
v___y_1160_ = v___x_1317_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
lean_dec(v_a_1315_);
v___x_1318_ = lean_box(0);
v___x_1319_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v_a_1286_);
v___y_1153_ = v_contextDependent_1310_;
v___y_1154_ = v_proof_1312_;
v___y_1155_ = v_e_x27_1308_;
v___y_1156_ = v_proof_1309_;
v___y_1157_ = v_snd_1283_;
v___y_1158_ = v_contextDependent_1313_;
v___y_1159_ = v_e_x27_1311_;
v___y_1160_ = v___x_1319_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_e_x27_1308_);
lean_dec_ref(v___x_1024_);
lean_dec(v_head_1006_);
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21);
lean_inc_ref(v_e_x27_1311_);
v___x_1321_ = l_Lean_mkApp5(v___x_1320_, v_arg_1023_, v_arg_1020_, v_e_x27_1311_, v_proof_1309_, v_proof_1312_);
if (v_contextDependent_1310_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_980_ = v___x_1322_;
v___y_981_ = v___x_1321_;
v___y_982_ = v_snd_1283_;
v___y_983_ = v_e_x27_1311_;
v___y_984_ = v_contextDependent_1313_;
goto v___jp_979_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_980_ = v___x_1323_;
v___y_981_ = v___x_1321_;
v___y_982_ = v_snd_1283_;
v___y_983_ = v_e_x27_1311_;
v___y_984_ = v___x_1143_;
goto v___jp_979_;
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_proof_1312_);
lean_dec_ref(v_e_x27_1311_);
lean_dec_ref(v_proof_1309_);
lean_dec_ref(v_e_x27_1308_);
lean_dec(v_a_1286_);
lean_dec(v_snd_1283_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1324_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1314_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1314_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
else
{
lean_inc(v_head_1006_);
lean_dec(v_a_1286_);
lean_dec(v_snd_1283_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_infos_934_);
if (lean_obj_tag(v_a_1176_) == 0)
{
uint8_t v_contextDependent_1332_; 
v_contextDependent_1332_ = lean_ctor_get_uint8(v_a_1176_, 1);
lean_dec_ref(v_a_1176_);
v___y_1145_ = v_fst_1282_;
v___y_1146_ = v___y_1279_;
v___y_1147_ = v_contextDependent_1332_;
goto v___jp_1144_;
}
else
{
uint8_t v_contextDependent_1333_; 
v_contextDependent_1333_ = lean_ctor_get_uint8(v_a_1176_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1176_);
v___y_1145_ = v_fst_1282_;
v___y_1146_ = v___y_1279_;
v___y_1147_ = v_contextDependent_1333_;
goto v___jp_1144_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_snd_1283_);
lean_dec(v_fst_1282_);
lean_dec(v_a_1176_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec_ref(v_infos_934_);
v_a_1334_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1285_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1285_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_dec(v_a_1176_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec_ref(v_infos_934_);
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_a_1176_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec_ref(v_infos_934_);
lean_dec_ref(v_simpBody_935_);
v_a_1412_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1178_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1178_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec_ref(v_infos_934_);
lean_dec_ref(v_simpBody_935_);
v_a_1420_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1175_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1175_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
v___jp_1025_:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_939_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1045_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1045_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1045_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_u_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v_u_1034_ = lean_ctor_get(v_head_1006_, 1);
lean_inc(v_u_1034_);
lean_dec(v_head_1006_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1));
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_u_1034_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_mkConst(v___x_1035_, v___x_1037_);
v___x_1039_ = l_Lean_mkApp3(v___x_1038_, v_arg_1023_, v_arg_1020_, v_proof_1026_);
v___x_1040_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1040_, 0, v_a_1030_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
lean_ctor_set_uint8(v___x_1040_, sizeof(void*)*2, v___y_1027_);
lean_ctor_set_uint8(v___x_1040_, sizeof(void*)*2 + 1, v___y_1028_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1036_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1041_);
v___x_1043_ = v___x_1032_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_proof_1026_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1046_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1029_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1029_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
v___jp_1054_:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_939_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1073_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1073_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1073_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_u_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v_u_1062_ = lean_ctor_get(v_head_1006_, 1);
lean_inc(v_u_1062_);
lean_dec(v_head_1006_);
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3));
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_u_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_mkConst(v___x_1063_, v___x_1065_);
v___x_1067_ = l_Lean_Expr_app___override(v___x_1066_, v_arg_1023_);
v___x_1068_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1068_, 0, v_a_1058_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*2, v___y_1055_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*2 + 1, v___y_1056_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1064_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1069_);
v___x_1071_ = v___x_1060_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_arg_1023_);
lean_dec(v_head_1006_);
v_a_1074_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1057_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1057_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
v___jp_1082_:
{
lean_object* v___x_1088_; 
lean_inc_ref(v___y_1085_);
lean_inc_ref(v_arg_1023_);
lean_inc_ref(v___x_1024_);
v___x_1088_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1024_, v_arg_1023_, v___y_1085_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1103_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1103_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1103_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1093_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5));
v___x_1094_ = l_Lean_Expr_constLevels_x21(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1095_ = l_Lean_mkConst(v___x_1093_, v___x_1094_);
v___x_1096_ = l_Lean_mkApp4(v___x_1095_, v_arg_1023_, v_arg_1020_, v___y_1085_, v___y_1083_);
v___x_1097_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1097_, 0, v_a_1089_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*2, v___y_1087_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*2 + 1, v___y_1084_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v_head_1006_);
lean_ctor_set(v___x_1098_, 1, v___y_1086_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1099_);
v___x_1101_ = v___x_1091_;
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
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1104_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1088_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1088_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1118_; 
lean_inc_ref(v_arg_1020_);
lean_inc_ref(v___y_1114_);
lean_inc_ref(v___x_1024_);
v___x_1118_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1024_, v___y_1114_, v_arg_1020_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1133_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7));
v___x_1124_ = l_Lean_Expr_constLevels_x21(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1125_ = l_Lean_mkConst(v___x_1123_, v___x_1124_);
v___x_1126_ = l_Lean_mkApp4(v___x_1125_, v_arg_1023_, v___y_1114_, v_arg_1020_, v___y_1115_);
v___x_1127_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1127_, 0, v_a_1119_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*2, v___y_1117_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*2 + 1, v___y_1113_);
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_head_1006_);
lean_ctor_set(v___x_1128_, 1, v___y_1116_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1129_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1134_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1118_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1118_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
v___jp_1144_:
{
if (v___y_1147_ == 0)
{
if (lean_obj_tag(v___y_1145_) == 0)
{
uint8_t v_contextDependent_1148_; 
lean_dec_ref(v_arg_1020_);
v_contextDependent_1148_ = lean_ctor_get_uint8(v___y_1145_, 1);
lean_dec_ref(v___y_1145_);
v___y_1055_ = v___y_1146_;
v___y_1056_ = v_contextDependent_1148_;
goto v___jp_1054_;
}
else
{
lean_object* v_proof_1149_; uint8_t v_contextDependent_1150_; 
v_proof_1149_ = lean_ctor_get(v___y_1145_, 1);
lean_inc_ref(v_proof_1149_);
v_contextDependent_1150_ = lean_ctor_get_uint8(v___y_1145_, sizeof(void*)*2 + 1);
lean_dec_ref(v___y_1145_);
v_proof_1026_ = v_proof_1149_;
v___y_1027_ = v___y_1146_;
v___y_1028_ = v_contextDependent_1150_;
goto v___jp_1025_;
}
}
else
{
if (lean_obj_tag(v___y_1145_) == 0)
{
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_arg_1020_);
v___y_1055_ = v___y_1146_;
v___y_1056_ = v___x_1143_;
goto v___jp_1054_;
}
else
{
lean_object* v_proof_1151_; 
v_proof_1151_ = lean_ctor_get(v___y_1145_, 1);
lean_inc_ref(v_proof_1151_);
lean_dec_ref(v___y_1145_);
v_proof_1026_ = v_proof_1151_;
v___y_1027_ = v___y_1146_;
v___y_1028_ = v___x_1143_;
goto v___jp_1025_;
}
}
}
v___jp_1152_:
{
lean_object* v___x_1161_; 
lean_inc_ref(v___y_1159_);
lean_inc_ref(v___y_1155_);
lean_inc_ref(v___x_1024_);
v___x_1161_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1024_, v___y_1155_, v___y_1159_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9));
v___x_1164_ = l_Lean_Expr_constLevels_x21(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1165_ = l_Lean_mkConst(v___x_1163_, v___x_1164_);
v___x_1166_ = l_Lean_mkApp6(v___x_1165_, v_arg_1023_, v___y_1155_, v_arg_1020_, v___y_1159_, v___y_1156_, v___y_1154_);
if (v___y_1153_ == 0)
{
v___y_1009_ = v___y_1160_;
v___y_1010_ = v___y_1157_;
v___y_1011_ = v___x_1166_;
v___y_1012_ = v_a_1162_;
v___y_1013_ = v___y_1158_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v___y_1160_;
v___y_1010_ = v___y_1157_;
v___y_1011_ = v___x_1166_;
v___y_1012_ = v_a_1162_;
v___y_1013_ = v___x_1143_;
goto v___jp_1008_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1020_);
lean_dec(v_head_1006_);
v_a_1167_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1161_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1161_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
v___jp_1008_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1014_, 0, v___y_1012_);
lean_ctor_set(v___x_1014_, 1, v___y_1011_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*2, v___y_1009_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*2 + 1, v___y_1013_);
v___x_1015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_head_1006_);
lean_ctor_set(v___x_1015_, 1, v___y_1010_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
v___jp_946_:
{
lean_object* v___x_956_; 
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
v___x_956_ = lean_apply_11(v_simpBody_935_, v_e_933_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_965_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v_a_957_);
lean_ctor_set(v___x_961_, 1, v_infos_934_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_infos_934_);
v_a_966_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_956_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_956_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_975_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v_infos_934_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
v___jp_979_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_985_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_985_, 0, v___y_983_);
lean_ctor_set(v___x_985_, 1, v___y_981_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*2, v___y_980_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*2 + 1, v___y_984_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___y_982_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___boxed(lean_object* v_e_1428_, lean_object* v_infos_1429_, lean_object* v_simpBody_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_e_1428_, v_infos_1429_, v_simpBody_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(lean_object* v_f_1442_, lean_object* v_a_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_1442_, v_a_1443_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___boxed(lean_object* v_f_1455_, lean_object* v_a_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(v_f_1455_, v_a_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object* v_simpBody_1475_, lean_object* v_e_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = l_Lean_Expr_isArrow(v_e_1476_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_e_1476_);
lean_dec_ref(v_simpBody_1475_);
v___x_1488_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1488_, 0, v___x_1487_);
lean_ctor_set_uint8(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
lean_inc_ref(v_e_1476_);
v___x_1490_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_1476_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_arrow_1492_; lean_object* v_infos_1493_; lean_object* v_v_1494_; lean_object* v___x_1495_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v___x_1490_);
v_arrow_1492_ = lean_ctor_get(v_a_1491_, 0);
lean_inc_ref_n(v_arrow_1492_, 2);
v_infos_1493_ = lean_ctor_get(v_a_1491_, 1);
lean_inc(v_infos_1493_);
v_v_1494_ = lean_ctor_get(v_a_1491_, 2);
lean_inc(v_v_1494_);
lean_dec(v_a_1491_);
v___x_1495_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arrow_1492_, v_infos_1493_, v_simpBody_1475_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1553_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1553_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1553_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_fst_1500_; 
v_fst_1500_ = lean_ctor_get(v_a_1496_, 0);
lean_inc(v_fst_1500_);
if (lean_obj_tag(v_fst_1500_) == 0)
{
uint8_t v_contextDependent_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_dec(v_a_1496_);
lean_dec(v_v_1494_);
lean_dec_ref(v_arrow_1492_);
lean_dec_ref(v_e_1476_);
v_contextDependent_1501_ = lean_ctor_get_uint8(v_fst_1500_, 1);
lean_dec_ref(v_fst_1500_);
v___x_1502_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1487_, v_contextDependent_1501_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1502_);
v___x_1504_ = v___x_1498_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
else
{
lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1551_; 
lean_del_object(v___x_1498_);
v_snd_1506_ = lean_ctor_get(v_a_1496_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_a_1496_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_a_1496_, 0);
lean_dec(v_unused_1552_);
v___x_1508_ = v_a_1496_;
v_isShared_1509_ = v_isSharedCheck_1551_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_dec(v_a_1496_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1551_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_e_x27_1510_; lean_object* v_proof_1511_; uint8_t v_contextDependent_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1550_; 
v_e_x27_1510_ = lean_ctor_get(v_fst_1500_, 0);
v_proof_1511_ = lean_ctor_get(v_fst_1500_, 1);
v_contextDependent_1512_ = lean_ctor_get_uint8(v_fst_1500_, sizeof(void*)*2 + 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_fst_1500_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1514_ = v_fst_1500_;
v_isShared_1515_ = v_isSharedCheck_1550_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_proof_1511_);
lean_inc(v_e_x27_1510_);
lean_dec(v_fst_1500_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1550_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; 
lean_inc_ref(v_e_x27_1510_);
v___x_1516_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_x27_1510_, v_snd_1506_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1541_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1541_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1541_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_inc(v_v_1494_);
v___x_1521_ = l_Lean_mkSort(v_v_1494_);
v___x_1522_ = l_Lean_Level_succ___override(v_v_1494_);
v___x_1523_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1));
v___x_1524_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 1);
lean_ctor_set(v___x_1508_, 1, v___x_1524_);
lean_ctor_set(v___x_1508_, 0, v___x_1522_);
v___x_1526_ = v___x_1508_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_inc_ref(v___x_1526_);
v___x_1527_ = l_Lean_mkConst(v___x_1523_, v___x_1526_);
v___x_1528_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2));
v___x_1529_ = l_Lean_mkConst(v___x_1528_, v___x_1526_);
lean_inc_ref(v_arrow_1492_);
lean_inc_ref_n(v___x_1521_, 3);
lean_inc_ref(v___x_1529_);
v___x_1530_ = l_Lean_mkAppB(v___x_1529_, v___x_1521_, v_arrow_1492_);
lean_inc_ref(v_e_x27_1510_);
lean_inc_ref(v_e_1476_);
lean_inc_ref(v___x_1527_);
v___x_1531_ = l_Lean_mkApp6(v___x_1527_, v___x_1521_, v_e_1476_, v_arrow_1492_, v_e_x27_1510_, v___x_1530_, v_proof_1511_);
lean_inc_n(v_a_1517_, 2);
v___x_1532_ = l_Lean_mkAppB(v___x_1529_, v___x_1521_, v_a_1517_);
v___x_1533_ = l_Lean_mkApp6(v___x_1527_, v___x_1521_, v_e_1476_, v_e_x27_1510_, v_a_1517_, v___x_1531_, v___x_1532_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___x_1533_);
lean_ctor_set(v___x_1514_, 0, v_a_1517_);
v___x_1535_ = v___x_1514_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1517_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1539_, sizeof(void*)*2 + 1, v_contextDependent_1512_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*2, v___x_1487_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1535_);
v___x_1537_ = v___x_1519_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
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
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_del_object(v___x_1514_);
lean_dec_ref(v_proof_1511_);
lean_dec_ref(v_e_x27_1510_);
lean_del_object(v___x_1508_);
lean_dec(v_v_1494_);
lean_dec_ref(v_arrow_1492_);
lean_dec_ref(v_e_1476_);
v_a_1542_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1516_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1516_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
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
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_v_1494_);
lean_dec_ref(v_arrow_1492_);
lean_dec_ref(v_e_1476_);
v_a_1554_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1495_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1495_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v_e_1476_);
lean_dec_ref(v_simpBody_1475_);
v_a_1562_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1490_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1490_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed(lean_object* v_simpBody_1570_, lean_object* v_e_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v_simpBody_1570_, v_e_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(lean_object* v_x_1583_, uint8_t v_bi_1584_, lean_object* v_t_1585_, lean_object* v_b_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___y_1595_; lean_object* v___x_1598_; uint8_t v_debug_1599_; 
v___x_1598_ = lean_st_ref_get(v___y_1588_);
v_debug_1599_ = lean_ctor_get_uint8(v___x_1598_, sizeof(void*)*10);
lean_dec(v___x_1598_);
if (v_debug_1599_ == 0)
{
v___y_1595_ = v___y_1588_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1600_; 
lean_inc_ref(v_t_1585_);
v___x_1600_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1585_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v___x_1600_);
lean_inc_ref(v_b_1586_);
v___x_1601_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref(v___x_1601_);
v___y_1595_ = v___y_1588_;
goto v___jp_1594_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_b_1586_);
lean_dec_ref(v_t_1585_);
lean_dec(v_x_1583_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v_b_1586_);
lean_dec_ref(v_t_1585_);
lean_dec(v_x_1583_);
v_a_1610_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1600_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1600_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
v___jp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = l_Lean_Expr_forallE___override(v_x_1583_, v_t_1585_, v_b_1586_, v_bi_1584_);
v___x_1597_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1596_, v___y_1595_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg___boxed(lean_object* v_x_1618_, lean_object* v_bi_1619_, lean_object* v_t_1620_, lean_object* v_b_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v_bi_boxed_1629_; lean_object* v_res_1630_; 
v_bi_boxed_1629_ = lean_unbox(v_bi_1619_);
v_res_1630_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1618_, v_bi_boxed_1629_, v_t_1620_, v_b_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(lean_object* v_x_1631_, uint8_t v_bi_1632_, lean_object* v_t_1633_, lean_object* v_b_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1631_, v_bi_1632_, v_t_1633_, v_b_1634_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___boxed(lean_object* v_x_1646_, lean_object* v_bi_1647_, lean_object* v_t_1648_, lean_object* v_b_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v_bi_boxed_1660_; lean_object* v_res_1661_; 
v_bi_boxed_1660_ = lean_unbox(v_bi_1647_);
v_res_1661_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(v_x_1646_, v_bi_boxed_1660_, v_t_1648_, v_b_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
return v_res_1661_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_instMonadEIO(lean_box(0));
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_toApplicative_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1746_; 
v___x_1678_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0);
v___x_1679_ = l_StateRefT_x27_instMonad___redArg(v___x_1678_);
v_toApplicative_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1679_, 1);
lean_dec(v_unused_1747_);
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1746_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_toApplicative_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1746_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_toFunctor_1684_; lean_object* v_toSeq_1685_; lean_object* v_toSeqLeft_1686_; lean_object* v_toSeqRight_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1744_; 
v_toFunctor_1684_ = lean_ctor_get(v_toApplicative_1680_, 0);
v_toSeq_1685_ = lean_ctor_get(v_toApplicative_1680_, 2);
v_toSeqLeft_1686_ = lean_ctor_get(v_toApplicative_1680_, 3);
v_toSeqRight_1687_ = lean_ctor_get(v_toApplicative_1680_, 4);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_toApplicative_1680_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_toApplicative_1680_, 1);
lean_dec(v_unused_1745_);
v___x_1689_ = v_toApplicative_1680_;
v_isShared_1690_ = v_isSharedCheck_1744_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_toSeqRight_1687_);
lean_inc(v_toSeqLeft_1686_);
lean_inc(v_toSeq_1685_);
lean_inc(v_toFunctor_1684_);
lean_dec(v_toApplicative_1680_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1744_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___x_1700_; 
v___f_1691_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1));
v___f_1692_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1684_);
v___f_1693_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1693_, 0, v_toFunctor_1684_);
v___f_1694_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1694_, 0, v_toFunctor_1684_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___f_1693_);
lean_ctor_set(v___x_1695_, 1, v___f_1694_);
v___f_1696_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1696_, 0, v_toSeqRight_1687_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toSeqLeft_1686_);
v___f_1698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1698_, 0, v_toSeq_1685_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v___f_1696_);
lean_ctor_set(v___x_1689_, 3, v___f_1697_);
lean_ctor_set(v___x_1689_, 2, v___f_1698_);
lean_ctor_set(v___x_1689_, 1, v___f_1691_);
lean_ctor_set(v___x_1689_, 0, v___x_1695_);
v___x_1700_ = v___x_1689_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___f_1691_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v___f_1698_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___f_1697_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v___f_1696_);
v___x_1700_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v___f_1692_);
lean_ctor_set(v___x_1682_, 0, v___x_1700_);
v___x_1702_ = v___x_1682_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___f_1692_);
v___x_1702_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; lean_object* v_toApplicative_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1740_; 
v___x_1703_ = l_StateRefT_x27_instMonad___redArg(v___x_1702_);
v_toApplicative_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v___x_1703_, 1);
lean_dec(v_unused_1741_);
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1740_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_toApplicative_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1740_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_toFunctor_1708_; lean_object* v_toSeq_1709_; lean_object* v_toSeqLeft_1710_; lean_object* v_toSeqRight_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1738_; 
v_toFunctor_1708_ = lean_ctor_get(v_toApplicative_1704_, 0);
v_toSeq_1709_ = lean_ctor_get(v_toApplicative_1704_, 2);
v_toSeqLeft_1710_ = lean_ctor_get(v_toApplicative_1704_, 3);
v_toSeqRight_1711_ = lean_ctor_get(v_toApplicative_1704_, 4);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_toApplicative_1704_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v_toApplicative_1704_, 1);
lean_dec(v_unused_1739_);
v___x_1713_ = v_toApplicative_1704_;
v_isShared_1714_ = v_isSharedCheck_1738_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_toSeqRight_1711_);
lean_inc(v_toSeqLeft_1710_);
lean_inc(v_toSeq_1709_);
lean_inc(v_toFunctor_1708_);
lean_dec(v_toApplicative_1704_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1738_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___x_1724_; 
v___f_1715_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3));
v___f_1716_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1708_);
v___f_1717_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1717_, 0, v_toFunctor_1708_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toFunctor_1708_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___f_1717_);
lean_ctor_set(v___x_1719_, 1, v___f_1718_);
v___f_1720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1720_, 0, v_toSeqRight_1711_);
v___f_1721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1721_, 0, v_toSeqLeft_1710_);
v___f_1722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1722_, 0, v_toSeq_1709_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 4, v___f_1720_);
lean_ctor_set(v___x_1713_, 3, v___f_1721_);
lean_ctor_set(v___x_1713_, 2, v___f_1722_);
lean_ctor_set(v___x_1713_, 1, v___f_1715_);
lean_ctor_set(v___x_1713_, 0, v___x_1719_);
v___x_1724_ = v___x_1713_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___f_1715_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v___f_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v___f_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v___f_1720_);
v___x_1724_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1726_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v___f_1716_);
lean_ctor_set(v___x_1706_, 0, v___x_1724_);
v___x_1726_ = v___x_1706_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___f_1716_);
v___x_1726_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_23189__overap_1734_; lean_object* v___x_1735_; 
v___x_1727_ = l_StateRefT_x27_instMonad___redArg(v___x_1726_);
v___x_1728_ = l_ReaderT_instMonad___redArg(v___x_1727_);
v___x_1729_ = l_StateRefT_x27_instMonad___redArg(v___x_1728_);
v___x_1730_ = l_ReaderT_instMonad___redArg(v___x_1729_);
v___x_1731_ = l_ReaderT_instMonad___redArg(v___x_1730_);
v___x_1732_ = l_Lean_instInhabitedExpr;
v___x_1733_ = l_instInhabitedOfMonad___redArg(v___x_1731_, v___x_1732_);
v___x_23189__overap_1734_ = lean_panic_fn_borrowed(v___x_1733_, v_msg_1667_);
lean_dec(v___x_1733_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
v___x_1735_ = lean_apply_10(v___x_23189__overap_1734_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, lean_box(0));
return v___x_1735_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___boxed(lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v_msg_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
return v_res_1759_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1766_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__4));
v___x_1767_ = lean_unsigned_to_nat(31u);
v___x_1768_ = lean_unsigned_to_nat(160u);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__3));
v___x_1770_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__2));
v___x_1771_ = l_mkPanicMessageWithDecl(v___x_1770_, v___x_1769_, v___x_1768_, v___x_1767_, v___x_1766_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow(lean_object* v_e_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
uint8_t v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1804_; uint8_t v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v_p_1810_; lean_object* v___x_1811_; 
v_p_1810_ = l_Lean_Expr_bindingDomain_x21(v_e_1778_);
lean_inc(v_a_1787_);
lean_inc_ref(v_a_1786_);
lean_inc(v_a_1785_);
lean_inc_ref(v_a_1784_);
lean_inc(v_a_1783_);
lean_inc_ref(v_a_1782_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_p_1810_);
v___x_1811_ = lean_sym_simp(v_p_1810_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v_q_1813_; lean_object* v___x_1814_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
v_q_1813_ = l_Lean_Expr_bindingBody_x21(v_e_1778_);
lean_inc(v_a_1787_);
lean_inc_ref(v_a_1786_);
lean_inc(v_a_1785_);
lean_inc_ref(v_a_1784_);
lean_inc(v_a_1783_);
lean_inc_ref(v_a_1782_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_q_1813_);
v___x_1814_ = lean_sym_simp(v_q_1813_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1994_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1994_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1994_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
uint8_t v___y_1820_; 
if (lean_obj_tag(v_a_1812_) == 0)
{
if (lean_obj_tag(v_a_1815_) == 0)
{
uint8_t v_contextDependent_1825_; 
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_contextDependent_1825_ = lean_ctor_get_uint8(v_a_1812_, 1);
lean_dec_ref(v_a_1812_);
if (v_contextDependent_1825_ == 0)
{
uint8_t v_contextDependent_1826_; 
v_contextDependent_1826_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref(v_a_1815_);
v___y_1820_ = v_contextDependent_1826_;
goto v___jp_1819_;
}
else
{
lean_dec_ref(v_a_1815_);
v___y_1820_ = v_contextDependent_1825_;
goto v___jp_1819_;
}
}
else
{
uint8_t v_contextDependent_1827_; lean_object* v_e_x27_1828_; lean_object* v_proof_1829_; uint8_t v_contextDependent_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1817_);
v_contextDependent_1827_ = lean_ctor_get_uint8(v_a_1812_, 1);
lean_dec_ref(v_a_1812_);
v_e_x27_1828_ = lean_ctor_get(v_a_1815_, 0);
lean_inc_ref(v_e_x27_1828_);
v_proof_1829_ = lean_ctor_get(v_a_1815_, 1);
lean_inc_ref(v_proof_1829_);
v_contextDependent_1830_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1815_);
lean_inc_ref(v_p_1810_);
v___x_1831_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1810_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
lean_inc_ref(v_q_1813_);
v___x_1833_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1813_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v_a_1836_; lean_object* v___y_1845_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
if (lean_obj_tag(v_e_1778_) == 7)
{
lean_object* v_binderName_1855_; lean_object* v_binderType_1856_; lean_object* v_body_1857_; uint8_t v_binderInfo_1858_; uint8_t v___y_1860_; uint8_t v___x_1862_; 
v_binderName_1855_ = lean_ctor_get(v_e_1778_, 0);
v_binderType_1856_ = lean_ctor_get(v_e_1778_, 1);
v_body_1857_ = lean_ctor_get(v_e_1778_, 2);
v_binderInfo_1858_ = lean_ctor_get_uint8(v_e_1778_, sizeof(void*)*3 + 8);
v___x_1862_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1856_, v_p_1810_);
if (v___x_1862_ == 0)
{
v___y_1860_ = v___x_1862_;
goto v___jp_1859_;
}
else
{
uint8_t v___x_1863_; 
v___x_1863_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1857_, v_e_x27_1828_);
v___y_1860_ = v___x_1863_;
goto v___jp_1859_;
}
v___jp_1859_:
{
if (v___y_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_inc(v_binderName_1855_);
lean_dec_ref(v_e_1778_);
lean_inc_ref(v_e_x27_1828_);
lean_inc_ref(v_p_1810_);
v___x_1861_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1855_, v_binderInfo_1858_, v_p_1810_, v_e_x27_1828_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1845_ = v___x_1861_;
goto v___jp_1844_;
}
else
{
v_a_1836_ = v_e_1778_;
goto v___jp_1835_;
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec_ref(v_e_1778_);
v___x_1864_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1865_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1864_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1845_ = v___x_1865_;
goto v___jp_1844_;
}
v___jp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1837_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__1));
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1834_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1832_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_mkConst(v___x_1837_, v___x_1840_);
v___x_1842_ = l_Lean_mkApp4(v___x_1841_, v_p_1810_, v_q_1813_, v_e_x27_1828_, v_proof_1829_);
v___x_1843_ = 0;
if (v_contextDependent_1827_ == 0)
{
v___y_1797_ = v___x_1843_;
v___y_1798_ = v_a_1836_;
v___y_1799_ = v___x_1842_;
v___y_1800_ = v_contextDependent_1830_;
goto v___jp_1796_;
}
else
{
v___y_1797_ = v___x_1843_;
v___y_1798_ = v_a_1836_;
v___y_1799_ = v___x_1842_;
v___y_1800_ = v_contextDependent_1827_;
goto v___jp_1796_;
}
}
v___jp_1844_:
{
if (lean_obj_tag(v___y_1845_) == 0)
{
lean_object* v_a_1846_; 
v_a_1846_ = lean_ctor_get(v___y_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___y_1845_);
v_a_1836_ = v_a_1846_;
goto v___jp_1835_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1834_);
lean_dec(v_a_1832_);
lean_dec_ref(v_proof_1829_);
lean_dec_ref(v_e_x27_1828_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
v_a_1847_ = lean_ctor_get(v___y_1845_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___y_1845_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___y_1845_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___y_1845_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_proof_1829_);
lean_dec_ref(v_e_x27_1828_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1866_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1833_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1833_);
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
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_proof_1829_);
lean_dec_ref(v_e_x27_1828_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1874_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1831_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1831_);
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
}
else
{
lean_del_object(v___x_1817_);
if (lean_obj_tag(v_a_1815_) == 0)
{
lean_object* v_e_x27_1882_; lean_object* v_proof_1883_; uint8_t v_contextDependent_1884_; uint8_t v_contextDependent_1885_; lean_object* v___x_1886_; 
v_e_x27_1882_ = lean_ctor_get(v_a_1812_, 0);
lean_inc_ref(v_e_x27_1882_);
v_proof_1883_ = lean_ctor_get(v_a_1812_, 1);
lean_inc_ref(v_proof_1883_);
v_contextDependent_1884_ = lean_ctor_get_uint8(v_a_1812_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1812_);
v_contextDependent_1885_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref(v_a_1815_);
lean_inc_ref(v_p_1810_);
v___x_1886_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1810_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
lean_inc_ref(v_q_1813_);
v___x_1888_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1813_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v_a_1891_; lean_object* v___y_1900_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
if (lean_obj_tag(v_e_1778_) == 7)
{
lean_object* v_binderName_1910_; lean_object* v_binderType_1911_; lean_object* v_body_1912_; uint8_t v_binderInfo_1913_; uint8_t v___y_1915_; uint8_t v___x_1917_; 
v_binderName_1910_ = lean_ctor_get(v_e_1778_, 0);
v_binderType_1911_ = lean_ctor_get(v_e_1778_, 1);
v_body_1912_ = lean_ctor_get(v_e_1778_, 2);
v_binderInfo_1913_ = lean_ctor_get_uint8(v_e_1778_, sizeof(void*)*3 + 8);
v___x_1917_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1911_, v_e_x27_1882_);
if (v___x_1917_ == 0)
{
v___y_1915_ = v___x_1917_;
goto v___jp_1914_;
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1912_, v_q_1813_);
v___y_1915_ = v___x_1918_;
goto v___jp_1914_;
}
v___jp_1914_:
{
if (v___y_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_inc(v_binderName_1910_);
lean_dec_ref(v_e_1778_);
lean_inc_ref(v_q_1813_);
lean_inc_ref(v_e_x27_1882_);
v___x_1916_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1910_, v_binderInfo_1913_, v_e_x27_1882_, v_q_1813_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1900_ = v___x_1916_;
goto v___jp_1899_;
}
else
{
v_a_1891_ = v_e_1778_;
goto v___jp_1890_;
}
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_e_1778_);
v___x_1919_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1920_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1919_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1900_ = v___x_1920_;
goto v___jp_1899_;
}
v___jp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1892_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__7));
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1889_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_a_1887_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_mkConst(v___x_1892_, v___x_1895_);
v___x_1897_ = l_Lean_mkApp4(v___x_1896_, v_p_1810_, v_e_x27_1882_, v_q_1813_, v_proof_1883_);
v___x_1898_ = 0;
if (v_contextDependent_1884_ == 0)
{
v___y_1790_ = v___x_1898_;
v___y_1791_ = v_a_1891_;
v___y_1792_ = v___x_1897_;
v___y_1793_ = v_contextDependent_1885_;
goto v___jp_1789_;
}
else
{
v___y_1790_ = v___x_1898_;
v___y_1791_ = v_a_1891_;
v___y_1792_ = v___x_1897_;
v___y_1793_ = v_contextDependent_1884_;
goto v___jp_1789_;
}
}
v___jp_1899_:
{
if (lean_obj_tag(v___y_1900_) == 0)
{
lean_object* v_a_1901_; 
v_a_1901_ = lean_ctor_get(v___y_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___y_1900_);
v_a_1891_ = v_a_1901_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1889_);
lean_dec(v_a_1887_);
lean_dec_ref(v_proof_1883_);
lean_dec_ref(v_e_x27_1882_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
v_a_1902_ = lean_ctor_get(v___y_1900_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1900_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___y_1900_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___y_1900_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1887_);
lean_dec_ref(v_proof_1883_);
lean_dec_ref(v_e_x27_1882_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1921_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1888_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1888_);
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
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_proof_1883_);
lean_dec_ref(v_e_x27_1882_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1929_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1886_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1886_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_e_x27_1937_; lean_object* v_proof_1938_; uint8_t v_contextDependent_1939_; lean_object* v_e_x27_1940_; lean_object* v_proof_1941_; uint8_t v_contextDependent_1942_; lean_object* v___x_1943_; 
v_e_x27_1937_ = lean_ctor_get(v_a_1812_, 0);
lean_inc_ref(v_e_x27_1937_);
v_proof_1938_ = lean_ctor_get(v_a_1812_, 1);
lean_inc_ref(v_proof_1938_);
v_contextDependent_1939_ = lean_ctor_get_uint8(v_a_1812_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1812_);
v_e_x27_1940_ = lean_ctor_get(v_a_1815_, 0);
lean_inc_ref(v_e_x27_1940_);
v_proof_1941_ = lean_ctor_get(v_a_1815_, 1);
lean_inc_ref(v_proof_1941_);
v_contextDependent_1942_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1815_);
lean_inc_ref(v_p_1810_);
v___x_1943_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1810_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
lean_inc_ref(v_q_1813_);
v___x_1945_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1813_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v_a_1948_; lean_object* v___y_1957_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
if (lean_obj_tag(v_e_1778_) == 7)
{
lean_object* v_binderName_1967_; lean_object* v_binderType_1968_; lean_object* v_body_1969_; uint8_t v_binderInfo_1970_; uint8_t v___y_1972_; uint8_t v___x_1974_; 
v_binderName_1967_ = lean_ctor_get(v_e_1778_, 0);
v_binderType_1968_ = lean_ctor_get(v_e_1778_, 1);
v_body_1969_ = lean_ctor_get(v_e_1778_, 2);
v_binderInfo_1970_ = lean_ctor_get_uint8(v_e_1778_, sizeof(void*)*3 + 8);
v___x_1974_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1968_, v_e_x27_1937_);
if (v___x_1974_ == 0)
{
v___y_1972_ = v___x_1974_;
goto v___jp_1971_;
}
else
{
uint8_t v___x_1975_; 
v___x_1975_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1969_, v_e_x27_1940_);
v___y_1972_ = v___x_1975_;
goto v___jp_1971_;
}
v___jp_1971_:
{
if (v___y_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_inc(v_binderName_1967_);
lean_dec_ref(v_e_1778_);
lean_inc_ref(v_e_x27_1940_);
lean_inc_ref(v_e_x27_1937_);
v___x_1973_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1967_, v_binderInfo_1970_, v_e_x27_1937_, v_e_x27_1940_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1957_ = v___x_1973_;
goto v___jp_1956_;
}
else
{
v_a_1948_ = v_e_1778_;
goto v___jp_1947_;
}
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref(v_e_1778_);
v___x_1976_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1977_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1976_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1957_ = v___x_1977_;
goto v___jp_1956_;
}
v___jp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1949_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__9));
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1946_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1944_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = l_Lean_mkConst(v___x_1949_, v___x_1952_);
v___x_1954_ = l_Lean_mkApp6(v___x_1953_, v_p_1810_, v_e_x27_1937_, v_q_1813_, v_e_x27_1940_, v_proof_1938_, v_proof_1941_);
v___x_1955_ = 0;
if (v_contextDependent_1939_ == 0)
{
v___y_1804_ = v___x_1954_;
v___y_1805_ = v___x_1955_;
v___y_1806_ = v_a_1948_;
v___y_1807_ = v_contextDependent_1942_;
goto v___jp_1803_;
}
else
{
v___y_1804_ = v___x_1954_;
v___y_1805_ = v___x_1955_;
v___y_1806_ = v_a_1948_;
v___y_1807_ = v_contextDependent_1939_;
goto v___jp_1803_;
}
}
v___jp_1956_:
{
if (lean_obj_tag(v___y_1957_) == 0)
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___y_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___y_1957_);
v_a_1948_ = v_a_1958_;
goto v___jp_1947_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1946_);
lean_dec(v_a_1944_);
lean_dec_ref(v_proof_1941_);
lean_dec_ref(v_e_x27_1940_);
lean_dec_ref(v_proof_1938_);
lean_dec_ref(v_e_x27_1937_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
v_a_1959_ = lean_ctor_get(v___y_1957_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___y_1957_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___y_1957_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___y_1957_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_a_1944_);
lean_dec_ref(v_proof_1941_);
lean_dec_ref(v_e_x27_1940_);
lean_dec_ref(v_proof_1938_);
lean_dec_ref(v_e_x27_1937_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1978_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1945_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1945_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v_proof_1941_);
lean_dec_ref(v_e_x27_1940_);
lean_dec_ref(v_proof_1938_);
lean_dec_ref(v_e_x27_1937_);
lean_dec_ref(v_q_1813_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1986_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1943_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1943_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
v___jp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1820_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1821_);
v___x_1823_ = v___x_1817_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_dec_ref(v_q_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
return v___x_1814_;
}
}
else
{
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
return v___x_1811_;
}
v___jp_1789_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1794_, 0, v___y_1791_);
lean_ctor_set(v___x_1794_, 1, v___y_1792_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*2, v___y_1790_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*2 + 1, v___y_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
v___jp_1796_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1801_, 0, v___y_1798_);
lean_ctor_set(v___x_1801_, 1, v___y_1799_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*2, v___y_1797_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*2 + 1, v___y_1800_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
v___jp_1803_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1808_, 0, v___y_1806_);
lean_ctor_set(v___x_1808_, 1, v___y_1804_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*2, v___y_1805_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*2 + 1, v___y_1807_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow___boxed(lean_object* v_e_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Meta_Sym_Simp_simpArrow(v_e_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(lean_object* v_simpBody_2007_, lean_object* v_xs_2008_, lean_object* v_b_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; 
lean_inc(v_a_2018_);
lean_inc_ref(v_a_2017_);
lean_inc(v_a_2016_);
lean_inc_ref(v_a_2015_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_b_2009_);
v___x_2020_ = lean_apply_11(v_simpBody_2007_, v_b_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, lean_box(0));
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2111_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2111_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2111_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
if (lean_obj_tag(v_a_2021_) == 0)
{
uint8_t v_contextDependent_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_xs_2008_);
v_contextDependent_2025_ = lean_ctor_get_uint8(v_a_2021_, 1);
lean_dec_ref(v_a_2021_);
v___x_2026_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2025_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2026_);
v___x_2028_ = v___x_2023_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
else
{
lean_object* v_e_x27_2030_; lean_object* v_proof_2031_; uint8_t v_contextDependent_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2023_);
v_e_x27_2030_ = lean_ctor_get(v_a_2021_, 0);
v_proof_2031_ = lean_ctor_get(v_a_2021_, 1);
v_contextDependent_2032_ = lean_ctor_get_uint8(v_a_2021_, sizeof(void*)*2 + 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2034_ = v_a_2021_;
v_isShared_2035_ = v_isSharedCheck_2110_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_proof_2031_);
lean_inc(v_e_x27_2030_);
lean_dec(v_a_2021_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2110_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v___x_2036_; uint8_t v___x_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2036_ = 0;
v___x_2037_ = 1;
v___x_2038_ = 1;
v___x_2039_ = l_Lean_Meta_mkLambdaFVars(v_xs_2008_, v_proof_2031_, v___x_2036_, v___x_2037_, v___x_2036_, v___x_2037_, v___x_2038_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2039_);
lean_inc_ref(v_e_x27_2030_);
v___x_2041_ = l_Lean_Meta_mkForallFVars(v_xs_2008_, v_e_x27_2030_, v___x_2036_, v___x_2037_, v___x_2037_, v___x_2038_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
v___x_2043_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2042_, v_a_2014_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
lean_inc_ref(v_xs_2008_);
v___x_2045_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_2008_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2045_);
v___x_2047_ = l_Lean_Meta_mkLambdaFVars(v_xs_2008_, v_b_2009_, v___x_2036_, v___x_2037_, v___x_2036_, v___x_2037_, v___x_2038_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = l_Lean_Meta_mkLambdaFVars(v_xs_2008_, v_e_x27_2030_, v___x_2036_, v___x_2037_, v___x_2036_, v___x_2037_, v___x_2038_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec_ref(v_xs_2008_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2061_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2061_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2061_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_mkApp3(v_a_2046_, v_a_2048_, v_a_2050_, v_a_2040_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2054_);
lean_ctor_set(v___x_2034_, 0, v_a_2044_);
v___x_2056_ = v___x_2034_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2044_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2054_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*2 + 1, v_contextDependent_2032_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*2, v___x_2036_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2056_);
v___x_2058_ = v___x_2052_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_2048_);
lean_dec(v_a_2046_);
lean_dec(v_a_2044_);
lean_dec(v_a_2040_);
lean_del_object(v___x_2034_);
v_a_2062_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2049_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2049_);
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
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_a_2046_);
lean_dec(v_a_2044_);
lean_dec(v_a_2040_);
lean_del_object(v___x_2034_);
lean_dec_ref(v_e_x27_2030_);
lean_dec_ref(v_xs_2008_);
v_a_2070_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2047_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2047_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_2044_);
lean_dec(v_a_2040_);
lean_del_object(v___x_2034_);
lean_dec_ref(v_e_x27_2030_);
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_xs_2008_);
v_a_2078_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2045_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2045_);
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
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_a_2040_);
lean_del_object(v___x_2034_);
lean_dec_ref(v_e_x27_2030_);
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_xs_2008_);
v_a_2086_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2043_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2043_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_a_2040_);
lean_del_object(v___x_2034_);
lean_dec_ref(v_e_x27_2030_);
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_xs_2008_);
v_a_2094_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2041_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2041_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_2034_);
lean_dec_ref(v_e_x27_2030_);
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_xs_2008_);
v_a_2102_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2039_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2039_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_xs_2008_);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main___boxed(lean_object* v_simpBody_2112_, lean_object* v_xs_2113_, lean_object* v_b_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2112_, v_xs_2113_, v_b_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(lean_object* v_e_2126_, lean_object* v_n_2127_){
_start:
{
if (lean_obj_tag(v_e_2126_) == 7)
{
lean_object* v_body_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_body_2128_ = lean_ctor_get(v_e_2126_, 2);
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_expr_has_loose_bvar(v_body_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
return v_n_2127_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = lean_nat_add(v_n_2127_, v___x_2131_);
lean_dec(v_n_2127_);
v_e_2126_ = v_body_2128_;
v_n_2127_ = v___x_2132_;
goto _start;
}
}
else
{
return v_n_2127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize___boxed(lean_object* v_e_2134_, lean_object* v_n_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v_e_2134_, v_n_2135_);
lean_dec_ref(v_e_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(lean_object* v_k_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v_b_2143_, lean_object* v_c_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
lean_inc(v___y_2140_);
lean_inc_ref(v___y_2139_);
lean_inc(v___y_2138_);
v___x_2150_ = lean_apply_12(v_k_2137_, v_b_2143_, v_c_2144_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, lean_box(0));
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v_b_2157_, lean_object* v_c_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(v_k_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v_b_2157_, v_c_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(lean_object* v_type_2165_, lean_object* v_maxFVars_x3f_2166_, lean_object* v_k_2167_, uint8_t v_cleanupAnnotations_2168_, uint8_t v_whnfType_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___f_2180_; lean_object* v___x_2181_; 
lean_inc(v___y_2174_);
lean_inc_ref(v___y_2173_);
lean_inc(v___y_2172_);
lean_inc_ref(v___y_2171_);
lean_inc(v___y_2170_);
v___f_2180_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2180_, 0, v_k_2167_);
lean_closure_set(v___f_2180_, 1, v___y_2170_);
lean_closure_set(v___f_2180_, 2, v___y_2171_);
lean_closure_set(v___f_2180_, 3, v___y_2172_);
lean_closure_set(v___f_2180_, 4, v___y_2173_);
lean_closure_set(v___f_2180_, 5, v___y_2174_);
v___x_2181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2165_, v_maxFVars_x3f_2166_, v___f_2180_, v_cleanupAnnotations_2168_, v_whnfType_2169_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2181_) == 0)
{
return v___x_2181_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___boxed(lean_object* v_type_2190_, lean_object* v_maxFVars_x3f_2191_, lean_object* v_k_2192_, lean_object* v_cleanupAnnotations_2193_, lean_object* v_whnfType_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2205_; uint8_t v_whnfType_boxed_2206_; lean_object* v_res_2207_; 
v_cleanupAnnotations_boxed_2205_ = lean_unbox(v_cleanupAnnotations_2193_);
v_whnfType_boxed_2206_ = lean_unbox(v_whnfType_2194_);
v_res_2207_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2190_, v_maxFVars_x3f_2191_, v_k_2192_, v_cleanupAnnotations_boxed_2205_, v_whnfType_boxed_2206_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(lean_object* v_00_u03b1_2208_, lean_object* v_type_2209_, lean_object* v_maxFVars_x3f_2210_, lean_object* v_k_2211_, uint8_t v_cleanupAnnotations_2212_, uint8_t v_whnfType_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2209_, v_maxFVars_x3f_2210_, v_k_2211_, v_cleanupAnnotations_2212_, v_whnfType_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___boxed(lean_object* v_00_u03b1_2225_, lean_object* v_type_2226_, lean_object* v_maxFVars_x3f_2227_, lean_object* v_k_2228_, lean_object* v_cleanupAnnotations_2229_, lean_object* v_whnfType_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2241_; uint8_t v_whnfType_boxed_2242_; lean_object* v_res_2243_; 
v_cleanupAnnotations_boxed_2241_ = lean_unbox(v_cleanupAnnotations_2229_);
v_whnfType_boxed_2242_ = lean_unbox(v_whnfType_2230_);
v_res_2243_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(v_00_u03b1_2225_, v_type_2226_, v_maxFVars_x3f_2227_, v_k_2228_, v_cleanupAnnotations_boxed_2241_, v_whnfType_boxed_2242_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(lean_object* v___y_2244_, lean_object* v_transientCache_2245_, lean_object* v_funext_2246_, lean_object* v_a_x3f_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v_numSteps_2250_; lean_object* v_persistentCache_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2261_; 
v___x_2249_ = lean_st_ref_take(v___y_2244_);
v_numSteps_2250_ = lean_ctor_get(v___x_2249_, 0);
v_persistentCache_2251_ = lean_ctor_get(v___x_2249_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2262_ = lean_ctor_get(v___x_2249_, 3);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v___x_2249_, 2);
lean_dec(v_unused_2263_);
v___x_2253_ = v___x_2249_;
v_isShared_2254_ = v_isSharedCheck_2261_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_persistentCache_2251_);
lean_inc(v_numSteps_2250_);
lean_dec(v___x_2249_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2261_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 3, v_funext_2246_);
lean_ctor_set(v___x_2253_, 2, v_transientCache_2245_);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_numSteps_2250_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_persistentCache_2251_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_transientCache_2245_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_funext_2246_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_st_ref_set(v___y_2244_, v___x_2256_);
v___x_2258_ = lean_box(0);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0___boxed(lean_object* v___y_2264_, lean_object* v_transientCache_2265_, lean_object* v_funext_2266_, lean_object* v_a_x3f_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2264_, v_transientCache_2265_, v_funext_2266_, v_a_x3f_2267_);
lean_dec(v_a_x3f_2267_);
lean_dec(v___y_2264_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(lean_object* v_simpBody_2270_, lean_object* v_xs_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v_transientCache_2285_; lean_object* v_funext_2286_; lean_object* v_a_2288_; lean_object* v___x_2299_; 
v___x_2283_ = lean_st_ref_get(v___y_2275_);
v___x_2284_ = lean_st_ref_get(v___y_2275_);
v_transientCache_2285_ = lean_ctor_get(v___x_2283_, 2);
lean_inc_ref(v_transientCache_2285_);
lean_dec(v___x_2283_);
v_funext_2286_ = lean_ctor_get(v___x_2284_, 3);
lean_inc_ref(v_funext_2286_);
lean_dec(v___x_2284_);
v___x_2299_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_2272_, v___y_2277_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2270_, v_xs_2271_, v_a_2300_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2318_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2318_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2318_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
lean_inc(v_a_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 1);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v___x_2308_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2275_, v_transientCache_2285_, v_funext_2286_, v___x_2307_);
lean_dec_ref(v___x_2307_);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v___x_2308_, 0);
lean_dec(v_unused_2316_);
v___x_2310_ = v___x_2308_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v___x_2308_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v_a_2302_);
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2302_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2301_);
v_a_2288_ = v_a_2319_;
goto v___jp_2287_;
}
}
else
{
lean_object* v_a_2320_; 
lean_dec_ref(v_xs_2271_);
lean_dec_ref(v_simpBody_2270_);
v_a_2320_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2299_);
v_a_2288_ = v_a_2320_;
goto v___jp_2287_;
}
v___jp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2275_, v_transientCache_2285_, v_funext_2286_, v___x_2289_);
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
lean_ctor_set_tag(v___x_2292_, 1);
lean_ctor_set(v___x_2292_, 0, v_a_2288_);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2288_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed(lean_object* v_simpBody_2321_, lean_object* v_xs_2322_, lean_object* v_b_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(v_simpBody_2321_, v_xs_2322_, v_b_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object* v_simpArrow_2335_, lean_object* v_simpBody_2336_, lean_object* v_e_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = l_Lean_Expr_isArrow(v_e_2337_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec_ref(v_simpArrow_2335_);
lean_inc_ref(v_e_2337_);
v___x_2349_ = l_Lean_Meta_isProp(v_e_2337_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2367_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2367_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2367_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_unbox(v_a_2350_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2359_; 
lean_dec_ref(v_e_2337_);
lean_dec_ref(v_simpBody_2336_);
v___x_2355_ = lean_alloc_ctor(0, 0, 2);
v___x_2356_ = lean_unbox(v_a_2350_);
lean_ctor_set_uint8(v___x_2355_, 0, v___x_2356_);
v___x_2357_ = lean_unbox(v_a_2350_);
lean_dec(v_a_2350_);
lean_ctor_set_uint8(v___x_2355_, 1, v___x_2357_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2355_);
v___x_2359_ = v___x_2352_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2355_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
else
{
lean_object* v___f_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_del_object(v___x_2352_);
lean_dec(v_a_2350_);
v___f_2361_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed), 13, 1);
lean_closure_set(v___f_2361_, 0, v_simpBody_2336_);
v___x_2362_ = l_Lean_Expr_bindingBody_x21(v_e_2337_);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v___x_2362_, v___x_2363_);
lean_dec_ref(v___x_2362_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
v___x_2366_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_e_2337_, v___x_2365_, v___f_2361_, v___x_2348_, v___x_2348_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v_e_2337_);
lean_dec_ref(v_simpBody_2336_);
v_a_2368_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2349_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2349_);
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
else
{
lean_object* v___x_2376_; 
lean_dec_ref(v_simpBody_2336_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
lean_inc(v_a_2342_);
lean_inc_ref(v_a_2341_);
lean_inc(v_a_2340_);
lean_inc_ref(v_a_2339_);
lean_inc(v_a_2338_);
v___x_2376_ = lean_apply_11(v_simpArrow_2335_, v_e_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, lean_box(0));
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object* v_simpArrow_2377_, lean_object* v_simpBody_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v_simpArrow_2377_, v_simpBody_2378_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object* v_e_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__0));
v___x_2405_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__1));
v___x_2406_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v___x_2404_, v___x_2405_, v_e_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object* v_e_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
return v_res_2418_;
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
