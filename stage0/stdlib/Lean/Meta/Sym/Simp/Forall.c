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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v___x_57_, 1);
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
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = l_Lean_Meta_mkForallFVars(v_xs_13_, v___x_29_, v___x_21_, v___x_22_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_65_, 1);
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
lean_dec_ref_known(v___x_74_, 1);
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
lean_dec_ref_known(v___x_241_, 1);
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
lean_dec_ref_known(v___x_247_, 1);
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
lean_dec_ref_known(v___x_332_, 1);
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
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = l_Lean_Meta_getLevel(v_a_427_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___x_435_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
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
v_debug_542_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*11);
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
lean_dec_ref_known(v___x_543_, 1);
lean_inc_ref(v_a_529_);
v___x_544_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_dec_ref_known(v___x_544_, 1);
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
lean_dec_ref_known(v___x_581_, 1);
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
lean_object* v_binderName_633_; lean_object* v_binderType_634_; lean_object* v_body_635_; uint8_t v_binderInfo_636_; uint8_t v___x_637_; uint8_t v___x_638_; 
v_binderName_633_ = lean_ctor_get(v_e_600_, 0);
v_binderType_634_ = lean_ctor_get(v_e_600_, 1);
v_body_635_ = lean_ctor_get(v_e_600_, 2);
v_binderInfo_636_ = lean_ctor_get_uint8(v_e_600_, sizeof(void*)*3 + 8);
v___x_637_ = l_Lean_Expr_hasLooseBVars(v_body_635_);
v___x_638_ = lean_bool_not(v___x_637_);
if (v___x_638_ == 0)
{
v___y_609_ = v_a_602_;
v___y_610_ = v_a_603_;
v___y_611_ = v_a_604_;
v___y_612_ = v_a_605_;
v___y_613_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_639_; 
lean_inc_ref(v_body_635_);
lean_inc_ref(v_binderType_634_);
lean_inc(v_binderName_633_);
lean_dec_ref_known(v_e_600_, 3);
v___x_639_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_body_635_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_arrow_641_; lean_object* v_infos_642_; lean_object* v_v_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_694_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v_arrow_641_ = lean_ctor_get(v_a_640_, 0);
v_infos_642_ = lean_ctor_get(v_a_640_, 1);
v_v_643_ = lean_ctor_get(v_a_640_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_640_);
if (v_isSharedCheck_694_ == 0)
{
v___x_645_ = v_a_640_;
v_isShared_646_ = v_isSharedCheck_694_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_v_643_);
lean_inc(v_infos_642_);
lean_inc(v_arrow_641_);
lean_dec(v_a_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_694_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; 
lean_inc_ref(v_binderType_634_);
v___x_647_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_634_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_n(v_a_648_, 2);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_650_ = lean_box(0);
lean_inc(v_v_643_);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_v_643_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v_a_648_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v___x_649_, v___x_652_, v_a_602_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_a_654_, v_binderType_634_, v_arrow_641_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_669_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_669_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc(v_v_643_);
lean_inc(v_a_648_);
v___x_660_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_660_, 0, v_binderName_633_);
lean_ctor_set(v___x_660_, 1, v_a_648_);
lean_ctor_set(v___x_660_, 2, v_v_643_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*3, v_binderInfo_636_);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_infos_642_);
v___x_662_ = l_Lean_mkLevelIMax_x27(v_a_648_, v_v_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 2, v___x_662_);
lean_ctor_set(v___x_645_, 1, v___x_661_);
lean_ctor_set(v___x_645_, 0, v_a_656_);
v___x_664_ = v___x_645_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v___x_662_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_664_);
v___x_666_ = v___x_658_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_a_648_);
lean_del_object(v___x_645_);
lean_dec(v_v_643_);
lean_dec(v_infos_642_);
lean_dec(v_binderName_633_);
v_a_670_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_655_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_655_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_a_648_);
lean_del_object(v___x_645_);
lean_dec(v_v_643_);
lean_dec(v_infos_642_);
lean_dec_ref(v_arrow_641_);
lean_dec_ref(v_binderType_634_);
lean_dec(v_binderName_633_);
v_a_678_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_653_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_653_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_del_object(v___x_645_);
lean_dec(v_v_643_);
lean_dec(v_infos_642_);
lean_dec_ref(v_arrow_641_);
lean_dec_ref(v_binderType_634_);
lean_dec(v_binderName_633_);
v_a_686_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_647_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_647_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_dec_ref(v_binderType_634_);
lean_dec(v_binderName_633_);
return v___x_639_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___boxed(lean_object* v_e_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(lean_object* v_x_704_, uint8_t v_bi_705_, lean_object* v_t_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___y_716_; lean_object* v___x_719_; uint8_t v_debug_720_; 
v___x_719_ = lean_st_ref_get(v___y_709_);
v_debug_720_ = lean_ctor_get_uint8(v___x_719_, sizeof(void*)*11);
lean_dec(v___x_719_);
if (v_debug_720_ == 0)
{
v___y_716_ = v___y_709_;
goto v___jp_715_;
}
else
{
lean_object* v___x_721_; 
lean_inc_ref(v_t_706_);
v___x_721_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
lean_dec_ref_known(v___x_721_, 1);
lean_inc_ref(v_b_707_);
v___x_722_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_dec_ref_known(v___x_722_, 1);
v___y_716_ = v___y_709_;
goto v___jp_715_;
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_b_707_);
lean_dec_ref(v_t_706_);
lean_dec(v_x_704_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_b_707_);
lean_dec_ref(v_t_706_);
lean_dec(v_x_704_);
v_a_731_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_721_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_721_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = l_Lean_Expr_forallE___override(v_x_704_, v_t_706_, v_b_707_, v_bi_705_);
v___x_718_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_717_, v___y_716_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0___boxed(lean_object* v_x_739_, lean_object* v_bi_740_, lean_object* v_t_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
uint8_t v_bi_boxed_750_; lean_object* v_res_751_; 
v_bi_boxed_750_ = lean_unbox(v_bi_740_);
v_res_751_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_x_739_, v_bi_boxed_750_, v_t_741_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(lean_object* v_e_752_, lean_object* v_infos_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
if (lean_obj_tag(v_infos_753_) == 1)
{
lean_object* v_head_761_; lean_object* v_tail_762_; lean_object* v_binderName_763_; uint8_t v_binderInfo_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_head_761_ = lean_ctor_get(v_infos_753_, 0);
lean_inc(v_head_761_);
v_tail_762_ = lean_ctor_get(v_infos_753_, 1);
lean_inc(v_tail_762_);
lean_dec_ref_known(v_infos_753_, 2);
v_binderName_763_ = lean_ctor_get(v_head_761_, 0);
lean_inc(v_binderName_763_);
v_binderInfo_764_ = lean_ctor_get_uint8(v_head_761_, sizeof(void*)*3);
lean_dec(v_head_761_);
lean_inc_ref(v_e_752_);
v___x_765_ = l_Lean_Expr_cleanupAnnotations(v_e_752_);
v___x_766_ = l_Lean_Expr_isApp(v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v___x_765_);
lean_dec(v_binderName_763_);
lean_dec(v_tail_762_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_e_752_);
return v___x_767_;
}
else
{
lean_object* v_arg_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_arg_768_ = lean_ctor_get(v___x_765_, 1);
lean_inc_ref(v_arg_768_);
v___x_769_ = l_Lean_Expr_appFnCleanup___redArg(v___x_765_);
v___x_770_ = l_Lean_Expr_isApp(v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v___x_769_);
lean_dec_ref(v_arg_768_);
lean_dec(v_binderName_763_);
lean_dec(v_tail_762_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_e_752_);
return v___x_771_;
}
else
{
lean_object* v_arg_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_arg_772_ = lean_ctor_get(v___x_769_, 1);
lean_inc_ref(v_arg_772_);
v___x_773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_769_);
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_775_ = l_Lean_Expr_isConstOf(v___x_773_, v___x_774_);
lean_dec_ref(v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v_arg_772_);
lean_dec_ref(v_arg_768_);
lean_dec(v_binderName_763_);
lean_dec(v_tail_762_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_e_752_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; 
lean_dec_ref(v_e_752_);
v___x_777_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_arg_768_, v_tail_762_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_binderName_763_, v_binderInfo_764_, v_arg_772_, v_a_778_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
return v___x_779_;
}
else
{
lean_dec_ref(v_arg_772_);
lean_dec(v_binderName_763_);
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v___x_780_; 
lean_dec(v_infos_753_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_e_752_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall___boxed(lean_object* v_e_781_, lean_object* v_infos_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_781_, v_infos_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(lean_object* v_head_791_, lean_object* v_00___792_){
_start:
{
lean_object* v_v_793_; uint8_t v___x_794_; 
v_v_793_ = lean_ctor_get(v_head_791_, 2);
v___x_794_ = l_Lean_Level_isZero(v_v_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0___boxed(lean_object* v_head_795_, lean_object* v_00___796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_795_, v_00___796_);
lean_dec_ref(v_head_795_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(lean_object* v_f_799_, lean_object* v_a_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___y_809_; lean_object* v___x_812_; uint8_t v_debug_813_; 
v___x_812_ = lean_st_ref_get(v___y_802_);
v_debug_813_ = lean_ctor_get_uint8(v___x_812_, sizeof(void*)*11);
lean_dec(v___x_812_);
if (v_debug_813_ == 0)
{
v___y_809_ = v___y_802_;
goto v___jp_808_;
}
else
{
lean_object* v___x_814_; 
lean_inc_ref(v_f_799_);
v___x_814_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_799_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v___x_815_; 
lean_dec_ref_known(v___x_814_, 1);
lean_inc_ref(v_a_800_);
v___x_815_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref_known(v___x_815_, 1);
v___y_809_ = v___y_802_;
goto v___jp_808_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_a_800_);
lean_dec_ref(v_f_799_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec_ref(v_a_800_);
lean_dec_ref(v_f_799_);
v_a_824_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_814_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_814_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
v___jp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = l_Lean_Expr_app___override(v_f_799_, v_a_800_);
v___x_811_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_810_, v___y_809_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(lean_object* v_f_832_, lean_object* v_a_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_832_, v_a_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(lean_object* v_f_842_, lean_object* v_a_u2081_843_, lean_object* v_a_u2082_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_842_, v_a_u2081_843_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_a_856_, v_a_u2082_844_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v___x_857_;
}
else
{
lean_dec_ref(v_a_u2082_844_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(lean_object* v_f_858_, lean_object* v_a_u2081_859_, lean_object* v_a_u2082_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v_f_858_, v_a_u2081_859_, v_a_u2082_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_box(0);
v___x_897_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11));
v___x_898_ = l_Lean_mkConst(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14));
v___x_905_ = l_Lean_mkConst(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = lean_box(0);
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17));
v___x_912_ = l_Lean_mkConst(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20));
v___x_919_ = l_Lean_mkConst(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_box(0);
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23));
v___x_926_ = l_Lean_mkConst(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_box(0);
v___x_932_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26));
v___x_933_ = l_Lean_mkConst(v___x_932_, v___x_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(lean_object* v_e_934_, lean_object* v_infos_935_, lean_object* v_simpBody_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; uint8_t v___y_976_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v___y_983_; lean_object* v___y_984_; uint8_t v___y_985_; 
if (lean_obj_tag(v_infos_935_) == 0)
{
lean_object* v___x_989_; 
lean_inc(v_a_945_);
lean_inc_ref(v_a_944_);
lean_inc(v_a_943_);
lean_inc_ref(v_a_942_);
lean_inc(v_a_941_);
lean_inc_ref(v_a_940_);
lean_inc(v_a_939_);
lean_inc_ref(v_a_938_);
lean_inc(v_a_937_);
v___x_989_ = lean_apply_11(v_simpBody_936_, v_e_934_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, lean_box(0));
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_998_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_a_990_);
lean_ctor_set(v___x_994_, 1, v_infos_935_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_a_999_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_989_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_989_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_head_1007_; lean_object* v_tail_1008_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; uint8_t v___y_1013_; uint8_t v___y_1014_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_head_1007_ = lean_ctor_get(v_infos_935_, 0);
v_tail_1008_ = lean_ctor_get(v_infos_935_, 1);
lean_inc_ref(v_e_934_);
v___x_1019_ = l_Lean_Expr_cleanupAnnotations(v_e_934_);
v___x_1020_ = l_Lean_Expr_isApp(v___x_1019_);
if (v___x_1020_ == 0)
{
lean_dec_ref(v___x_1019_);
v___y_948_ = v_a_937_;
v___y_949_ = v_a_938_;
v___y_950_ = v_a_939_;
v___y_951_ = v_a_940_;
v___y_952_ = v_a_941_;
v___y_953_ = v_a_942_;
v___y_954_ = v_a_943_;
v___y_955_ = v_a_944_;
v___y_956_ = v_a_945_;
goto v___jp_947_;
}
else
{
lean_object* v_arg_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_arg_1021_ = lean_ctor_get(v___x_1019_, 1);
lean_inc_ref(v_arg_1021_);
v___x_1022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1019_);
v___x_1023_ = l_Lean_Expr_isApp(v___x_1022_);
if (v___x_1023_ == 0)
{
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_arg_1021_);
v___y_948_ = v_a_937_;
v___y_949_ = v_a_938_;
v___y_950_ = v_a_939_;
v___y_951_ = v_a_940_;
v___y_952_ = v_a_941_;
v___y_953_ = v_a_942_;
v___y_954_ = v_a_943_;
v___y_955_ = v_a_944_;
v___y_956_ = v_a_945_;
goto v___jp_947_;
}
else
{
lean_object* v_arg_1024_; lean_object* v___x_1025_; uint8_t v___y_1027_; lean_object* v_proof_1028_; uint8_t v___y_1029_; uint8_t v___y_1056_; uint8_t v___y_1057_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v___y_1118_; lean_object* v___x_1143_; uint8_t v___x_1144_; uint8_t v___y_1146_; lean_object* v___y_1147_; uint8_t v___y_1148_; lean_object* v___y_1154_; lean_object* v___y_1155_; uint8_t v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; uint8_t v___y_1160_; uint8_t v___y_1161_; 
v_arg_1024_ = lean_ctor_get(v___x_1022_, 1);
lean_inc_ref(v_arg_1024_);
v___x_1025_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1022_);
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_1144_ = l_Lean_Expr_isConstOf(v___x_1025_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
v___y_948_ = v_a_937_;
v___y_949_ = v_a_938_;
v___y_950_ = v_a_939_;
v___y_951_ = v_a_940_;
v___y_952_ = v_a_941_;
v___y_953_ = v_a_942_;
v___y_954_ = v_a_943_;
v___y_955_ = v_a_944_;
v___y_956_ = v_a_945_;
goto v___jp_947_;
}
else
{
lean_object* v___x_1176_; 
lean_dec_ref(v_e_934_);
lean_inc(v_a_945_);
lean_inc_ref(v_a_944_);
lean_inc(v_a_943_);
lean_inc_ref(v_a_942_);
lean_inc(v_a_941_);
lean_inc_ref(v_a_940_);
lean_inc(v_a_939_);
lean_inc_ref(v_a_938_);
lean_inc(v_a_937_);
lean_inc_ref(v_arg_1024_);
v___x_1176_ = lean_sym_simp(v_arg_1024_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1024_, v_a_1177_);
v___x_1179_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v___x_1178_, v_a_940_);
lean_dec_ref(v___x_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___y_1182_; uint8_t v___y_1183_; uint8_t v___y_1184_; lean_object* v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1253_; uint8_t v___y_1280_; uint8_t v___x_1343_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1343_ = lean_unbox(v_a_1180_);
if (v___x_1343_ == 0)
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_unbox(v_a_1180_);
lean_dec(v_a_1180_);
v___y_1280_ = v___x_1344_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
lean_dec(v_a_1180_);
v___x_1345_ = lean_box(0);
v___x_1346_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1007_, v___x_1345_);
if (v___x_1346_ == 0)
{
v___y_1280_ = v___x_1346_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_simpBody_936_);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_infos_935_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; lean_object* v_unused_1412_; 
v_unused_1411_ = lean_ctor_get(v_infos_935_, 1);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_infos_935_, 0);
lean_dec(v_unused_1412_);
v___x_1348_ = v_infos_935_;
v_isShared_1349_ = v_isSharedCheck_1410_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v_infos_935_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1410_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
if (lean_obj_tag(v_a_1177_) == 0)
{
uint8_t v_contextDependent_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v_arg_1024_);
v_contextDependent_1350_ = lean_ctor_get_uint8(v_a_1177_, 1);
lean_dec_ref_known(v_a_1177_, 0);
v___x_1351_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_940_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1367_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1367_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1367_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24);
v___x_1358_ = l_Lean_Expr_app___override(v___x_1357_, v_arg_1021_);
v___x_1359_ = 0;
v___x_1360_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1360_, 0, v_a_1352_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*2, v___x_1359_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*2 + 1, v_contextDependent_1350_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 0);
lean_ctor_set(v___x_1348_, 1, v___x_1356_);
lean_ctor_set(v___x_1348_, 0, v___x_1360_);
v___x_1362_ = v___x_1348_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1356_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1362_);
v___x_1364_ = v___x_1354_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1348_);
lean_dec_ref(v_arg_1021_);
v_a_1368_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1351_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1351_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_proof_1376_; uint8_t v_contextDependent_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1408_; 
v_proof_1376_ = lean_ctor_get(v_a_1177_, 1);
v_contextDependent_1377_ = lean_ctor_get_uint8(v_a_1177_, sizeof(void*)*2 + 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_a_1177_, 0);
lean_dec(v_unused_1409_);
v___x_1379_ = v_a_1177_;
v_isShared_1380_ = v_isSharedCheck_1408_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_proof_1376_);
lean_dec(v_a_1177_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1408_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_940_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1399_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1399_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1399_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1391_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27);
v___x_1388_ = l_Lean_mkApp3(v___x_1387_, v_arg_1024_, v_arg_1021_, v_proof_1376_);
v___x_1389_ = 0;
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___x_1388_);
lean_ctor_set(v___x_1379_, 0, v_a_1382_);
v___x_1391_ = v___x_1379_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1382_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*2 + 1, v_contextDependent_1377_);
v___x_1391_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*2, v___x_1389_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 0);
lean_ctor_set(v___x_1348_, 1, v___x_1386_);
lean_ctor_set(v___x_1348_, 0, v___x_1391_);
v___x_1393_ = v___x_1348_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1386_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1393_);
v___x_1395_ = v___x_1384_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1379_);
lean_dec_ref(v_proof_1376_);
lean_del_object(v___x_1348_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
v_a_1400_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1381_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1381_);
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
}
}
}
}
v___jp_1181_:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1024_, v_a_940_);
lean_dec_ref(v_arg_1024_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1208_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1208_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1208_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_unbox(v_a_1186_);
lean_dec(v_a_1186_);
if (v___x_1190_ == 0)
{
lean_del_object(v___x_1188_);
lean_dec(v___y_1182_);
lean_dec_ref(v_arg_1021_);
v___y_976_ = v___y_1184_;
goto v___jp_975_;
}
else
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1007_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_del_object(v___x_1188_);
lean_dec(v___y_1182_);
lean_dec_ref(v_arg_1021_);
v___y_976_ = v___y_1184_;
goto v___jp_975_;
}
else
{
lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1205_; 
v_isSharedCheck_1205_ = !lean_is_exclusive(v_infos_935_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1206_ = lean_ctor_get(v_infos_935_, 1);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_infos_935_, 0);
lean_dec(v_unused_1207_);
v___x_1194_ = v_infos_935_;
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v_infos_935_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1196_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12);
lean_inc_ref(v_arg_1021_);
v___x_1197_ = l_Lean_Expr_app___override(v___x_1196_, v_arg_1021_);
v___x_1198_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1198_, 0, v_arg_1021_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*2, v___y_1183_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*2 + 1, v___y_1184_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 0);
lean_ctor_set(v___x_1194_, 1, v___y_1182_);
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___y_1182_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1200_);
v___x_1202_ = v___x_1188_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v___y_1182_);
lean_dec_ref(v_arg_1021_);
lean_dec_ref_known(v_infos_935_, 2);
v_a_1209_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1185_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1185_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
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
v___jp_1217_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1024_, v_a_940_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1239_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1239_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1239_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_unbox(v_a_1224_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; 
lean_del_object(v___x_1226_);
v___x_1229_ = lean_unbox(v_a_1224_);
lean_dec(v_a_1224_);
v___y_1084_ = v___y_1218_;
v___y_1085_ = v___y_1222_;
v___y_1086_ = v___y_1220_;
v___y_1087_ = v___y_1221_;
v___y_1088_ = v___x_1229_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
lean_dec(v_a_1224_);
v___x_1230_ = lean_box(0);
v___x_1231_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1007_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_del_object(v___x_1226_);
v___y_1084_ = v___y_1218_;
v___y_1085_ = v___y_1222_;
v___y_1086_ = v___y_1220_;
v___y_1087_ = v___y_1221_;
v___y_1088_ = v___x_1231_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec(v_head_1007_);
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15);
lean_inc_ref(v___y_1221_);
v___x_1233_ = l_Lean_mkApp3(v___x_1232_, v_arg_1021_, v___y_1221_, v___y_1220_);
v___x_1234_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1234_, 0, v___y_1221_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*2, v___y_1219_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*2 + 1, v___y_1222_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___y_1218_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1235_);
v___x_1237_ = v___x_1226_;
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
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1218_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
v_a_1240_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1223_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1223_);
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
v___jp_1248_:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___y_1250_, v_a_940_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1270_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1270_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1270_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_unbox(v_a_1255_);
if (v___x_1259_ == 0)
{
uint8_t v___x_1260_; 
lean_del_object(v___x_1257_);
v___x_1260_ = lean_unbox(v_a_1255_);
lean_dec(v_a_1255_);
v___y_1114_ = v___y_1249_;
v___y_1115_ = v___y_1253_;
v___y_1116_ = v___y_1250_;
v___y_1117_ = v___y_1252_;
v___y_1118_ = v___x_1260_;
goto v___jp_1113_;
}
else
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
lean_dec(v_a_1255_);
v___x_1261_ = lean_box(0);
v___x_1262_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1007_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_del_object(v___x_1257_);
v___y_1114_ = v___y_1249_;
v___y_1115_ = v___y_1253_;
v___y_1116_ = v___y_1250_;
v___y_1117_ = v___y_1252_;
v___y_1118_ = v___x_1262_;
goto v___jp_1113_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___x_1025_);
lean_dec(v_head_1007_);
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18);
lean_inc_ref(v_arg_1021_);
v___x_1264_ = l_Lean_mkApp3(v___x_1263_, v_arg_1024_, v_arg_1021_, v___y_1252_);
v___x_1265_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1265_, 0, v_arg_1021_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*2, v___y_1251_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*2 + 1, v___y_1253_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___y_1249_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1266_);
v___x_1268_ = v___x_1257_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
v_a_1271_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1254_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1254_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; 
lean_inc(v_tail_1008_);
lean_inc_ref(v_arg_1021_);
v___x_1281_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arg_1021_, v_tail_1008_, v_simpBody_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v_fst_1283_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_fst_1283_);
v_snd_1284_ = lean_ctor_get(v_a_1282_, 1);
lean_inc(v_snd_1284_);
lean_dec(v_a_1282_);
v___x_1285_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1021_, v_fst_1283_);
v___x_1286_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___x_1285_, v_a_940_);
lean_dec_ref(v___x_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_unbox(v_a_1287_);
if (v___x_1288_ == 0)
{
if (lean_obj_tag(v_a_1177_) == 0)
{
if (lean_obj_tag(v_fst_1283_) == 0)
{
uint8_t v_contextDependent_1289_; 
lean_dec_ref(v___x_1025_);
v_contextDependent_1289_ = lean_ctor_get_uint8(v_a_1177_, 1);
lean_dec_ref_known(v_a_1177_, 0);
if (v_contextDependent_1289_ == 0)
{
uint8_t v_contextDependent_1290_; uint8_t v___x_1291_; 
v_contextDependent_1290_ = lean_ctor_get_uint8(v_fst_1283_, 1);
lean_dec_ref_known(v_fst_1283_, 0);
v___x_1291_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_1182_ = v_snd_1284_;
v___y_1183_ = v___x_1291_;
v___y_1184_ = v_contextDependent_1290_;
goto v___jp_1181_;
}
else
{
uint8_t v___x_1292_; 
lean_dec_ref_known(v_fst_1283_, 0);
v___x_1292_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_1182_ = v_snd_1284_;
v___y_1183_ = v___x_1292_;
v___y_1184_ = v___x_1144_;
goto v___jp_1181_;
}
}
else
{
uint8_t v_contextDependent_1293_; 
lean_inc(v_head_1007_);
lean_dec_ref_known(v_infos_935_, 2);
v_contextDependent_1293_ = lean_ctor_get_uint8(v_a_1177_, 1);
lean_dec_ref_known(v_a_1177_, 0);
if (v_contextDependent_1293_ == 0)
{
lean_object* v_e_x27_1294_; lean_object* v_proof_1295_; uint8_t v_contextDependent_1296_; uint8_t v___x_1297_; 
v_e_x27_1294_ = lean_ctor_get(v_fst_1283_, 0);
lean_inc_ref(v_e_x27_1294_);
v_proof_1295_ = lean_ctor_get(v_fst_1283_, 1);
lean_inc_ref(v_proof_1295_);
v_contextDependent_1296_ = lean_ctor_get_uint8(v_fst_1283_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1283_, 2);
v___x_1297_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_1218_ = v_snd_1284_;
v___y_1219_ = v___x_1297_;
v___y_1220_ = v_proof_1295_;
v___y_1221_ = v_e_x27_1294_;
v___y_1222_ = v_contextDependent_1296_;
goto v___jp_1217_;
}
else
{
lean_object* v_e_x27_1298_; lean_object* v_proof_1299_; uint8_t v___x_1300_; 
v_e_x27_1298_ = lean_ctor_get(v_fst_1283_, 0);
lean_inc_ref(v_e_x27_1298_);
v_proof_1299_ = lean_ctor_get(v_fst_1283_, 1);
lean_inc_ref(v_proof_1299_);
lean_dec_ref_known(v_fst_1283_, 2);
v___x_1300_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_1218_ = v_snd_1284_;
v___y_1219_ = v___x_1300_;
v___y_1220_ = v_proof_1299_;
v___y_1221_ = v_e_x27_1298_;
v___y_1222_ = v___x_1144_;
goto v___jp_1217_;
}
}
}
else
{
lean_inc(v_head_1007_);
lean_dec_ref_known(v_infos_935_, 2);
if (lean_obj_tag(v_fst_1283_) == 0)
{
uint8_t v_contextDependent_1301_; 
v_contextDependent_1301_ = lean_ctor_get_uint8(v_a_1177_, sizeof(void*)*2 + 1);
if (v_contextDependent_1301_ == 0)
{
lean_object* v_e_x27_1302_; lean_object* v_proof_1303_; uint8_t v_contextDependent_1304_; uint8_t v___x_1305_; 
v_e_x27_1302_ = lean_ctor_get(v_a_1177_, 0);
lean_inc_ref(v_e_x27_1302_);
v_proof_1303_ = lean_ctor_get(v_a_1177_, 1);
lean_inc_ref(v_proof_1303_);
lean_dec_ref_known(v_a_1177_, 2);
v_contextDependent_1304_ = lean_ctor_get_uint8(v_fst_1283_, 1);
lean_dec_ref_known(v_fst_1283_, 0);
v___x_1305_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_1249_ = v_snd_1284_;
v___y_1250_ = v_e_x27_1302_;
v___y_1251_ = v___x_1305_;
v___y_1252_ = v_proof_1303_;
v___y_1253_ = v_contextDependent_1304_;
goto v___jp_1248_;
}
else
{
lean_object* v_e_x27_1306_; lean_object* v_proof_1307_; uint8_t v___x_1308_; 
lean_dec_ref_known(v_fst_1283_, 0);
v_e_x27_1306_ = lean_ctor_get(v_a_1177_, 0);
lean_inc_ref(v_e_x27_1306_);
v_proof_1307_ = lean_ctor_get(v_a_1177_, 1);
lean_inc_ref(v_proof_1307_);
lean_dec_ref_known(v_a_1177_, 2);
v___x_1308_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_1249_ = v_snd_1284_;
v___y_1250_ = v_e_x27_1306_;
v___y_1251_ = v___x_1308_;
v___y_1252_ = v_proof_1307_;
v___y_1253_ = v___x_1144_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_e_x27_1309_; lean_object* v_proof_1310_; uint8_t v_contextDependent_1311_; lean_object* v_e_x27_1312_; lean_object* v_proof_1313_; uint8_t v_contextDependent_1314_; lean_object* v___x_1315_; 
v_e_x27_1309_ = lean_ctor_get(v_a_1177_, 0);
lean_inc_ref(v_e_x27_1309_);
v_proof_1310_ = lean_ctor_get(v_a_1177_, 1);
lean_inc_ref(v_proof_1310_);
v_contextDependent_1311_ = lean_ctor_get_uint8(v_a_1177_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1177_, 2);
v_e_x27_1312_ = lean_ctor_get(v_fst_1283_, 0);
lean_inc_ref(v_e_x27_1312_);
v_proof_1313_ = lean_ctor_get(v_fst_1283_, 1);
lean_inc_ref(v_proof_1313_);
v_contextDependent_1314_ = lean_ctor_get_uint8(v_fst_1283_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1283_, 2);
v___x_1315_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1309_, v_a_940_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; uint8_t v___x_1317_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = lean_unbox(v_a_1316_);
if (v___x_1317_ == 0)
{
uint8_t v___x_1318_; 
lean_dec(v_a_1287_);
v___x_1318_ = lean_unbox(v_a_1316_);
lean_dec(v_a_1316_);
v___y_1154_ = v_snd_1284_;
v___y_1155_ = v_proof_1313_;
v___y_1156_ = v_contextDependent_1311_;
v___y_1157_ = v_e_x27_1312_;
v___y_1158_ = v_e_x27_1309_;
v___y_1159_ = v_proof_1310_;
v___y_1160_ = v_contextDependent_1314_;
v___y_1161_ = v___x_1318_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
lean_dec(v_a_1316_);
v___x_1319_ = lean_box(0);
v___x_1320_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1007_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_dec(v_a_1287_);
v___y_1154_ = v_snd_1284_;
v___y_1155_ = v_proof_1313_;
v___y_1156_ = v_contextDependent_1311_;
v___y_1157_ = v_e_x27_1312_;
v___y_1158_ = v_e_x27_1309_;
v___y_1159_ = v_proof_1310_;
v___y_1160_ = v_contextDependent_1314_;
v___y_1161_ = v___x_1320_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v_e_x27_1309_);
lean_dec_ref(v___x_1025_);
lean_dec(v_head_1007_);
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21);
lean_inc_ref(v_e_x27_1312_);
v___x_1322_ = l_Lean_mkApp5(v___x_1321_, v_arg_1024_, v_arg_1021_, v_e_x27_1312_, v_proof_1310_, v_proof_1313_);
if (v_contextDependent_1311_ == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_981_ = v_snd_1284_;
v___y_982_ = v_e_x27_1312_;
v___y_983_ = v___x_1323_;
v___y_984_ = v___x_1322_;
v___y_985_ = v_contextDependent_1314_;
goto v___jp_980_;
}
else
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
v___y_981_ = v_snd_1284_;
v___y_982_ = v_e_x27_1312_;
v___y_983_ = v___x_1324_;
v___y_984_ = v___x_1322_;
v___y_985_ = v___x_1144_;
goto v___jp_980_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_proof_1313_);
lean_dec_ref(v_e_x27_1312_);
lean_dec_ref(v_proof_1310_);
lean_dec_ref(v_e_x27_1309_);
lean_dec(v_a_1287_);
lean_dec(v_snd_1284_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
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
}
else
{
lean_inc(v_head_1007_);
lean_dec(v_a_1287_);
lean_dec(v_snd_1284_);
lean_dec_ref(v___x_1025_);
lean_dec_ref_known(v_infos_935_, 2);
if (lean_obj_tag(v_a_1177_) == 0)
{
uint8_t v_contextDependent_1333_; 
v_contextDependent_1333_ = lean_ctor_get_uint8(v_a_1177_, 1);
lean_dec_ref_known(v_a_1177_, 0);
v___y_1146_ = v___y_1280_;
v___y_1147_ = v_fst_1283_;
v___y_1148_ = v_contextDependent_1333_;
goto v___jp_1145_;
}
else
{
uint8_t v_contextDependent_1334_; 
v_contextDependent_1334_ = lean_ctor_get_uint8(v_a_1177_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1177_, 2);
v___y_1146_ = v___y_1280_;
v___y_1147_ = v_fst_1283_;
v___y_1148_ = v_contextDependent_1334_;
goto v___jp_1145_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_snd_1284_);
lean_dec(v_fst_1283_);
lean_dec(v_a_1177_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec_ref_known(v_infos_935_, 2);
v_a_1335_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1286_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1286_);
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
lean_dec(v_a_1177_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec_ref_known(v_infos_935_, 2);
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_a_1177_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec_ref_known(v_infos_935_, 2);
lean_dec_ref(v_simpBody_936_);
v_a_1413_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1179_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1179_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec_ref_known(v_infos_935_, 2);
lean_dec_ref(v_simpBody_936_);
v_a_1421_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1176_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1176_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
v___jp_1026_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_940_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1046_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1046_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1046_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_u_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_u_1035_ = lean_ctor_get(v_head_1007_, 1);
lean_inc(v_u_1035_);
lean_dec(v_head_1007_);
v___x_1036_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1));
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_u_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_mkConst(v___x_1036_, v___x_1038_);
v___x_1040_ = l_Lean_mkApp3(v___x_1039_, v_arg_1024_, v_arg_1021_, v_proof_1028_);
v___x_1041_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1041_, 0, v_a_1031_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*2, v___y_1027_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*2 + 1, v___y_1029_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1037_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1042_);
v___x_1044_ = v___x_1033_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_proof_1028_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
v_a_1047_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1030_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1030_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
v___jp_1055_:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_940_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1074_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1074_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1074_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_u_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_u_1063_ = lean_ctor_get(v_head_1007_, 1);
lean_inc(v_u_1063_);
lean_dec(v_head_1007_);
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3));
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_u_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_mkConst(v___x_1064_, v___x_1066_);
v___x_1068_ = l_Lean_Expr_app___override(v___x_1067_, v_arg_1024_);
v___x_1069_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1069_, 0, v_a_1059_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*2, v___y_1056_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*2 + 1, v___y_1057_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1065_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1070_);
v___x_1072_ = v___x_1061_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_arg_1024_);
lean_dec(v_head_1007_);
v_a_1075_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1058_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1058_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
v___jp_1083_:
{
lean_object* v___x_1089_; 
lean_inc_ref(v___y_1087_);
lean_inc_ref(v_arg_1024_);
lean_inc_ref(v___x_1025_);
v___x_1089_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1025_, v_arg_1024_, v___y_1087_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1104_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1104_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1104_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5));
v___x_1095_ = l_Lean_Expr_constLevels_x21(v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1096_ = l_Lean_mkConst(v___x_1094_, v___x_1095_);
v___x_1097_ = l_Lean_mkApp4(v___x_1096_, v_arg_1024_, v_arg_1021_, v___y_1087_, v___y_1086_);
v___x_1098_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1098_, 0, v_a_1090_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2, v___y_1088_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2 + 1, v___y_1085_);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_head_1007_);
lean_ctor_set(v___x_1099_, 1, v___y_1084_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1100_);
v___x_1102_ = v___x_1092_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1084_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
v_a_1105_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1089_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1089_);
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
v___jp_1113_:
{
lean_object* v___x_1119_; 
lean_inc_ref(v_arg_1021_);
lean_inc_ref(v___y_1116_);
lean_inc_ref(v___x_1025_);
v___x_1119_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1025_, v___y_1116_, v_arg_1021_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1134_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1134_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1134_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7));
v___x_1125_ = l_Lean_Expr_constLevels_x21(v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1126_ = l_Lean_mkConst(v___x_1124_, v___x_1125_);
v___x_1127_ = l_Lean_mkApp4(v___x_1126_, v_arg_1024_, v___y_1116_, v_arg_1021_, v___y_1117_);
v___x_1128_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1128_, 0, v_a_1120_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*2, v___y_1118_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*2 + 1, v___y_1115_);
v___x_1129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_head_1007_);
lean_ctor_set(v___x_1129_, 1, v___y_1114_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1130_);
v___x_1132_ = v___x_1122_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1114_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
v_a_1135_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1119_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1119_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
v___jp_1145_:
{
if (v___y_1148_ == 0)
{
if (lean_obj_tag(v___y_1147_) == 0)
{
uint8_t v_contextDependent_1149_; 
lean_dec_ref(v_arg_1021_);
v_contextDependent_1149_ = lean_ctor_get_uint8(v___y_1147_, 1);
lean_dec_ref_known(v___y_1147_, 0);
v___y_1056_ = v___y_1146_;
v___y_1057_ = v_contextDependent_1149_;
goto v___jp_1055_;
}
else
{
lean_object* v_proof_1150_; uint8_t v_contextDependent_1151_; 
v_proof_1150_ = lean_ctor_get(v___y_1147_, 1);
lean_inc_ref(v_proof_1150_);
v_contextDependent_1151_ = lean_ctor_get_uint8(v___y_1147_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_1147_, 2);
v___y_1027_ = v___y_1146_;
v_proof_1028_ = v_proof_1150_;
v___y_1029_ = v_contextDependent_1151_;
goto v___jp_1026_;
}
}
else
{
if (lean_obj_tag(v___y_1147_) == 0)
{
lean_dec_ref_known(v___y_1147_, 0);
lean_dec_ref(v_arg_1021_);
v___y_1056_ = v___y_1146_;
v___y_1057_ = v___x_1144_;
goto v___jp_1055_;
}
else
{
lean_object* v_proof_1152_; 
v_proof_1152_ = lean_ctor_get(v___y_1147_, 1);
lean_inc_ref(v_proof_1152_);
lean_dec_ref_known(v___y_1147_, 2);
v___y_1027_ = v___y_1146_;
v_proof_1028_ = v_proof_1152_;
v___y_1029_ = v___x_1144_;
goto v___jp_1026_;
}
}
}
v___jp_1153_:
{
lean_object* v___x_1162_; 
lean_inc_ref(v___y_1157_);
lean_inc_ref(v___y_1158_);
lean_inc_ref(v___x_1025_);
v___x_1162_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1025_, v___y_1158_, v___y_1157_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9));
v___x_1165_ = l_Lean_Expr_constLevels_x21(v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1166_ = l_Lean_mkConst(v___x_1164_, v___x_1165_);
v___x_1167_ = l_Lean_mkApp6(v___x_1166_, v_arg_1024_, v___y_1158_, v_arg_1021_, v___y_1157_, v___y_1159_, v___y_1155_);
if (v___y_1156_ == 0)
{
v___y_1010_ = v___y_1154_;
v___y_1011_ = v___x_1167_;
v___y_1012_ = v_a_1163_;
v___y_1013_ = v___y_1161_;
v___y_1014_ = v___y_1160_;
goto v___jp_1009_;
}
else
{
v___y_1010_ = v___y_1154_;
v___y_1011_ = v___x_1167_;
v___y_1012_ = v_a_1163_;
v___y_1013_ = v___y_1161_;
v___y_1014_ = v___x_1144_;
goto v___jp_1009_;
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_arg_1021_);
lean_dec(v_head_1007_);
v_a_1168_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1162_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1162_);
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
}
}
v___jp_1009_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1015_, 0, v___y_1012_);
lean_ctor_set(v___x_1015_, 1, v___y_1011_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*2, v___y_1013_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*2 + 1, v___y_1014_);
v___x_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1016_, 0, v_head_1007_);
lean_ctor_set(v___x_1016_, 1, v___y_1010_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
v___jp_947_:
{
lean_object* v___x_957_; 
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
v___x_957_ = lean_apply_11(v_simpBody_936_, v_e_934_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v_a_958_);
lean_ctor_set(v___x_962_, 1, v_infos_935_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_infos_935_);
v_a_967_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_957_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_976_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_infos_935_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
v___jp_980_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_986_, 0, v___y_982_);
lean_ctor_set(v___x_986_, 1, v___y_984_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*2, v___y_983_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*2 + 1, v___y_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___y_981_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___boxed(lean_object* v_e_1429_, lean_object* v_infos_1430_, lean_object* v_simpBody_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_e_1429_, v_infos_1430_, v_simpBody_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(lean_object* v_f_1443_, lean_object* v_a_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_1443_, v_a_1444_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___boxed(lean_object* v_f_1456_, lean_object* v_a_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(v_f_1456_, v_a_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object* v_simpBody_1476_, lean_object* v_e_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Expr_isArrow(v_e_1477_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v_e_1477_);
lean_dec_ref(v_simpBody_1476_);
v___x_1489_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1489_, 0, v___x_1488_);
lean_ctor_set_uint8(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; 
lean_inc_ref(v_e_1477_);
v___x_1491_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_1477_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v_arrow_1493_; lean_object* v_infos_1494_; lean_object* v_v_1495_; lean_object* v___x_1496_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v_arrow_1493_ = lean_ctor_get(v_a_1492_, 0);
lean_inc_ref_n(v_arrow_1493_, 2);
v_infos_1494_ = lean_ctor_get(v_a_1492_, 1);
lean_inc(v_infos_1494_);
v_v_1495_ = lean_ctor_get(v_a_1492_, 2);
lean_inc(v_v_1495_);
lean_dec(v_a_1492_);
v___x_1496_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arrow_1493_, v_infos_1494_, v_simpBody_1476_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1554_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1554_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1554_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_fst_1501_; 
v_fst_1501_ = lean_ctor_get(v_a_1497_, 0);
lean_inc(v_fst_1501_);
if (lean_obj_tag(v_fst_1501_) == 0)
{
uint8_t v_contextDependent_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v_a_1497_);
lean_dec(v_v_1495_);
lean_dec_ref(v_arrow_1493_);
lean_dec_ref(v_e_1477_);
v_contextDependent_1502_ = lean_ctor_get_uint8(v_fst_1501_, 1);
lean_dec_ref_known(v_fst_1501_, 0);
v___x_1503_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1488_, v_contextDependent_1502_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1505_ = v___x_1499_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
else
{
lean_object* v_snd_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1552_; 
lean_del_object(v___x_1499_);
v_snd_1507_ = lean_ctor_get(v_a_1497_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_a_1497_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v_a_1497_, 0);
lean_dec(v_unused_1553_);
v___x_1509_ = v_a_1497_;
v_isShared_1510_ = v_isSharedCheck_1552_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snd_1507_);
lean_dec(v_a_1497_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1552_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_e_x27_1511_; lean_object* v_proof_1512_; uint8_t v_contextDependent_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1551_; 
v_e_x27_1511_ = lean_ctor_get(v_fst_1501_, 0);
v_proof_1512_ = lean_ctor_get(v_fst_1501_, 1);
v_contextDependent_1513_ = lean_ctor_get_uint8(v_fst_1501_, sizeof(void*)*2 + 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_fst_1501_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1515_ = v_fst_1501_;
v_isShared_1516_ = v_isSharedCheck_1551_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_proof_1512_);
lean_inc(v_e_x27_1511_);
lean_dec(v_fst_1501_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1551_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; 
lean_inc_ref(v_e_x27_1511_);
v___x_1517_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_x27_1511_, v_snd_1507_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1542_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1542_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1542_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_inc(v_v_1495_);
v___x_1522_ = l_Lean_mkSort(v_v_1495_);
v___x_1523_ = l_Lean_Level_succ___override(v_v_1495_);
v___x_1524_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1));
v___x_1525_ = lean_box(0);
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 1);
lean_ctor_set(v___x_1509_, 1, v___x_1525_);
lean_ctor_set(v___x_1509_, 0, v___x_1523_);
v___x_1527_ = v___x_1509_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
lean_inc_ref(v___x_1527_);
v___x_1528_ = l_Lean_mkConst(v___x_1524_, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2));
v___x_1530_ = l_Lean_mkConst(v___x_1529_, v___x_1527_);
lean_inc_ref(v_arrow_1493_);
lean_inc_ref_n(v___x_1522_, 3);
lean_inc_ref(v___x_1530_);
v___x_1531_ = l_Lean_mkAppB(v___x_1530_, v___x_1522_, v_arrow_1493_);
lean_inc_ref(v_e_x27_1511_);
lean_inc_ref(v_e_1477_);
lean_inc_ref(v___x_1528_);
v___x_1532_ = l_Lean_mkApp6(v___x_1528_, v___x_1522_, v_e_1477_, v_arrow_1493_, v_e_x27_1511_, v___x_1531_, v_proof_1512_);
lean_inc_n(v_a_1518_, 2);
v___x_1533_ = l_Lean_mkAppB(v___x_1530_, v___x_1522_, v_a_1518_);
v___x_1534_ = l_Lean_mkApp6(v___x_1528_, v___x_1522_, v_e_1477_, v_e_x27_1511_, v_a_1518_, v___x_1532_, v___x_1533_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1534_);
lean_ctor_set(v___x_1515_, 0, v_a_1518_);
v___x_1536_ = v___x_1515_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1518_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*2 + 1, v_contextDependent_1513_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*2, v___x_1488_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1536_);
v___x_1538_ = v___x_1520_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1515_);
lean_dec_ref(v_proof_1512_);
lean_dec_ref(v_e_x27_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_v_1495_);
lean_dec_ref(v_arrow_1493_);
lean_dec_ref(v_e_1477_);
v_a_1543_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1517_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1517_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
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
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_v_1495_);
lean_dec_ref(v_arrow_1493_);
lean_dec_ref(v_e_1477_);
v_a_1555_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1496_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1496_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_e_1477_);
lean_dec_ref(v_simpBody_1476_);
v_a_1563_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1491_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1491_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed(lean_object* v_simpBody_1571_, lean_object* v_e_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v_simpBody_1571_, v_e_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(lean_object* v_x_1584_, uint8_t v_bi_1585_, lean_object* v_t_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___y_1596_; lean_object* v___x_1599_; uint8_t v_debug_1600_; 
v___x_1599_ = lean_st_ref_get(v___y_1589_);
v_debug_1600_ = lean_ctor_get_uint8(v___x_1599_, sizeof(void*)*11);
lean_dec(v___x_1599_);
if (v_debug_1600_ == 0)
{
v___y_1596_ = v___y_1589_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1601_; 
lean_inc_ref(v_t_1586_);
v___x_1601_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1586_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref_known(v___x_1601_, 1);
lean_inc_ref(v_b_1587_);
v___x_1602_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_dec_ref_known(v___x_1602_, 1);
v___y_1596_ = v___y_1589_;
goto v___jp_1595_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_b_1587_);
lean_dec_ref(v_t_1586_);
lean_dec(v_x_1584_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_b_1587_);
lean_dec_ref(v_t_1586_);
lean_dec(v_x_1584_);
v_a_1611_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1601_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
v___jp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = l_Lean_Expr_forallE___override(v_x_1584_, v_t_1586_, v_b_1587_, v_bi_1585_);
v___x_1598_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1597_, v___y_1596_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg___boxed(lean_object* v_x_1619_, lean_object* v_bi_1620_, lean_object* v_t_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v_bi_boxed_1630_; lean_object* v_res_1631_; 
v_bi_boxed_1630_ = lean_unbox(v_bi_1620_);
v_res_1631_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1619_, v_bi_boxed_1630_, v_t_1621_, v_b_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(lean_object* v_x_1632_, uint8_t v_bi_1633_, lean_object* v_t_1634_, lean_object* v_b_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1632_, v_bi_1633_, v_t_1634_, v_b_1635_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___boxed(lean_object* v_x_1647_, lean_object* v_bi_1648_, lean_object* v_t_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
uint8_t v_bi_boxed_1661_; lean_object* v_res_1662_; 
v_bi_boxed_1661_ = lean_unbox(v_bi_1648_);
v_res_1662_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(v_x_1647_, v_bi_boxed_1661_, v_t_1649_, v_b_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
return v_res_1662_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_instMonadEIO(lean_box(0));
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(lean_object* v_msg_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_toApplicative_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1747_; 
v___x_1679_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0);
v___x_1680_ = l_StateRefT_x27_instMonad___redArg(v___x_1679_);
v_toApplicative_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v___x_1680_, 1);
lean_dec(v_unused_1748_);
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1747_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_toApplicative_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1747_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_toFunctor_1685_; lean_object* v_toSeq_1686_; lean_object* v_toSeqLeft_1687_; lean_object* v_toSeqRight_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1745_; 
v_toFunctor_1685_ = lean_ctor_get(v_toApplicative_1681_, 0);
v_toSeq_1686_ = lean_ctor_get(v_toApplicative_1681_, 2);
v_toSeqLeft_1687_ = lean_ctor_get(v_toApplicative_1681_, 3);
v_toSeqRight_1688_ = lean_ctor_get(v_toApplicative_1681_, 4);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_toApplicative_1681_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_dec(v_unused_1746_);
v___x_1690_ = v_toApplicative_1681_;
v_isShared_1691_ = v_isSharedCheck_1745_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_toSeqRight_1688_);
lean_inc(v_toSeqLeft_1687_);
lean_inc(v_toSeq_1686_);
lean_inc(v_toFunctor_1685_);
lean_dec(v_toApplicative_1681_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1745_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___x_1701_; 
v___f_1692_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1));
v___f_1693_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1685_);
v___f_1694_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1694_, 0, v_toFunctor_1685_);
v___f_1695_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1695_, 0, v_toFunctor_1685_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___f_1694_);
lean_ctor_set(v___x_1696_, 1, v___f_1695_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toSeqRight_1688_);
v___f_1698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1698_, 0, v_toSeqLeft_1687_);
v___f_1699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1699_, 0, v_toSeq_1686_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v___f_1697_);
lean_ctor_set(v___x_1690_, 3, v___f_1698_);
lean_ctor_set(v___x_1690_, 2, v___f_1699_);
lean_ctor_set(v___x_1690_, 1, v___f_1692_);
lean_ctor_set(v___x_1690_, 0, v___x_1696_);
v___x_1701_ = v___x_1690_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___f_1692_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v___f_1699_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v___f_1698_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v___f_1697_);
v___x_1701_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___f_1693_);
lean_ctor_set(v___x_1683_, 0, v___x_1701_);
v___x_1703_ = v___x_1683_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___f_1693_);
v___x_1703_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v_toApplicative_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1741_; 
v___x_1704_ = l_StateRefT_x27_instMonad___redArg(v___x_1703_);
v_toApplicative_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1704_, 1);
lean_dec(v_unused_1742_);
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1741_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_toApplicative_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1741_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_toFunctor_1709_; lean_object* v_toSeq_1710_; lean_object* v_toSeqLeft_1711_; lean_object* v_toSeqRight_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1739_; 
v_toFunctor_1709_ = lean_ctor_get(v_toApplicative_1705_, 0);
v_toSeq_1710_ = lean_ctor_get(v_toApplicative_1705_, 2);
v_toSeqLeft_1711_ = lean_ctor_get(v_toApplicative_1705_, 3);
v_toSeqRight_1712_ = lean_ctor_get(v_toApplicative_1705_, 4);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_toApplicative_1705_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_toApplicative_1705_, 1);
lean_dec(v_unused_1740_);
v___x_1714_ = v_toApplicative_1705_;
v_isShared_1715_ = v_isSharedCheck_1739_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_toSeqRight_1712_);
lean_inc(v_toSeqLeft_1711_);
lean_inc(v_toSeq_1710_);
lean_inc(v_toFunctor_1709_);
lean_dec(v_toApplicative_1705_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1739_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1725_; 
v___f_1716_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3));
v___f_1717_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1709_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toFunctor_1709_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toFunctor_1709_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___f_1718_);
lean_ctor_set(v___x_1720_, 1, v___f_1719_);
v___f_1721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1721_, 0, v_toSeqRight_1712_);
v___f_1722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1722_, 0, v_toSeqLeft_1711_);
v___f_1723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1723_, 0, v_toSeq_1710_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v___f_1721_);
lean_ctor_set(v___x_1714_, 3, v___f_1722_);
lean_ctor_set(v___x_1714_, 2, v___f_1723_);
lean_ctor_set(v___x_1714_, 1, v___f_1716_);
lean_ctor_set(v___x_1714_, 0, v___x_1720_);
v___x_1725_ = v___x_1714_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___f_1716_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v___f_1723_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v___f_1722_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v___f_1721_);
v___x_1725_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___f_1717_);
lean_ctor_set(v___x_1707_, 0, v___x_1725_);
v___x_1727_ = v___x_1707_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___f_1717_);
v___x_1727_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_23189__overap_1735_; lean_object* v___x_1736_; 
v___x_1728_ = l_StateRefT_x27_instMonad___redArg(v___x_1727_);
v___x_1729_ = l_ReaderT_instMonad___redArg(v___x_1728_);
v___x_1730_ = l_StateRefT_x27_instMonad___redArg(v___x_1729_);
v___x_1731_ = l_ReaderT_instMonad___redArg(v___x_1730_);
v___x_1732_ = l_ReaderT_instMonad___redArg(v___x_1731_);
v___x_1733_ = l_Lean_instInhabitedExpr;
v___x_1734_ = l_instInhabitedOfMonad___redArg(v___x_1732_, v___x_1733_);
v___x_23189__overap_1735_ = lean_panic_fn_borrowed(v___x_1734_, v_msg_1668_);
lean_dec(v___x_1734_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
v___x_1736_ = lean_apply_10(v___x_23189__overap_1735_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1736_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___boxed(lean_object* v_msg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
return v_res_1760_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1767_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__4));
v___x_1768_ = lean_unsigned_to_nat(31u);
v___x_1769_ = lean_unsigned_to_nat(160u);
v___x_1770_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__3));
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__2));
v___x_1772_ = l_mkPanicMessageWithDecl(v___x_1771_, v___x_1770_, v___x_1769_, v___x_1768_, v___x_1767_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow(lean_object* v_e_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v___y_1801_; lean_object* v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; lean_object* v_p_1811_; lean_object* v___x_1812_; 
v_p_1811_ = l_Lean_Expr_bindingDomain_x21(v_e_1779_);
lean_inc(v_a_1788_);
lean_inc_ref(v_a_1787_);
lean_inc(v_a_1786_);
lean_inc_ref(v_a_1785_);
lean_inc(v_a_1784_);
lean_inc_ref(v_a_1783_);
lean_inc(v_a_1782_);
lean_inc_ref(v_a_1781_);
lean_inc(v_a_1780_);
lean_inc_ref(v_p_1811_);
v___x_1812_ = lean_sym_simp(v_p_1811_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v_q_1814_; lean_object* v___x_1815_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v_q_1814_ = l_Lean_Expr_bindingBody_x21(v_e_1779_);
lean_inc(v_a_1788_);
lean_inc_ref(v_a_1787_);
lean_inc(v_a_1786_);
lean_inc_ref(v_a_1785_);
lean_inc(v_a_1784_);
lean_inc_ref(v_a_1783_);
lean_inc(v_a_1782_);
lean_inc_ref(v_a_1781_);
lean_inc(v_a_1780_);
lean_inc_ref(v_q_1814_);
v___x_1815_ = lean_sym_simp(v_q_1814_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1995_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1995_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1995_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___y_1821_; 
if (lean_obj_tag(v_a_1813_) == 0)
{
if (lean_obj_tag(v_a_1816_) == 0)
{
uint8_t v_contextDependent_1826_; 
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_contextDependent_1826_ = lean_ctor_get_uint8(v_a_1813_, 1);
lean_dec_ref_known(v_a_1813_, 0);
if (v_contextDependent_1826_ == 0)
{
uint8_t v_contextDependent_1827_; 
v_contextDependent_1827_ = lean_ctor_get_uint8(v_a_1816_, 1);
lean_dec_ref_known(v_a_1816_, 0);
v___y_1821_ = v_contextDependent_1827_;
goto v___jp_1820_;
}
else
{
lean_dec_ref_known(v_a_1816_, 0);
v___y_1821_ = v_contextDependent_1826_;
goto v___jp_1820_;
}
}
else
{
uint8_t v_contextDependent_1828_; lean_object* v_e_x27_1829_; lean_object* v_proof_1830_; uint8_t v_contextDependent_1831_; lean_object* v___x_1832_; 
lean_del_object(v___x_1818_);
v_contextDependent_1828_ = lean_ctor_get_uint8(v_a_1813_, 1);
lean_dec_ref_known(v_a_1813_, 0);
v_e_x27_1829_ = lean_ctor_get(v_a_1816_, 0);
lean_inc_ref(v_e_x27_1829_);
v_proof_1830_ = lean_ctor_get(v_a_1816_, 1);
lean_inc_ref(v_proof_1830_);
v_contextDependent_1831_ = lean_ctor_get_uint8(v_a_1816_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1816_, 2);
lean_inc_ref(v_p_1811_);
v___x_1832_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1811_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
lean_inc_ref(v_q_1814_);
v___x_1834_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1814_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_a_1837_; lean_object* v___y_1846_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
if (lean_obj_tag(v_e_1779_) == 7)
{
lean_object* v_binderName_1856_; lean_object* v_binderType_1857_; lean_object* v_body_1858_; uint8_t v_binderInfo_1859_; uint8_t v___y_1861_; uint8_t v___x_1863_; 
v_binderName_1856_ = lean_ctor_get(v_e_1779_, 0);
v_binderType_1857_ = lean_ctor_get(v_e_1779_, 1);
v_body_1858_ = lean_ctor_get(v_e_1779_, 2);
v_binderInfo_1859_ = lean_ctor_get_uint8(v_e_1779_, sizeof(void*)*3 + 8);
v___x_1863_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1857_, v_p_1811_);
if (v___x_1863_ == 0)
{
v___y_1861_ = v___x_1863_;
goto v___jp_1860_;
}
else
{
uint8_t v___x_1864_; 
v___x_1864_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1858_, v_e_x27_1829_);
v___y_1861_ = v___x_1864_;
goto v___jp_1860_;
}
v___jp_1860_:
{
if (v___y_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_inc(v_binderName_1856_);
lean_dec_ref_known(v_e_1779_, 3);
lean_inc_ref(v_e_x27_1829_);
lean_inc_ref(v_p_1811_);
v___x_1862_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1856_, v_binderInfo_1859_, v_p_1811_, v_e_x27_1829_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
v___y_1846_ = v___x_1862_;
goto v___jp_1845_;
}
else
{
v_a_1837_ = v_e_1779_;
goto v___jp_1836_;
}
}
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec_ref(v_e_1779_);
v___x_1865_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1866_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1865_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
v___y_1846_ = v___x_1866_;
goto v___jp_1845_;
}
v___jp_1836_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1838_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__1));
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1835_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1833_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_mkConst(v___x_1838_, v___x_1841_);
v___x_1843_ = l_Lean_mkApp4(v___x_1842_, v_p_1811_, v_q_1814_, v_e_x27_1829_, v_proof_1830_);
v___x_1844_ = 0;
if (v_contextDependent_1828_ == 0)
{
v___y_1798_ = v___x_1844_;
v___y_1799_ = v___x_1843_;
v___y_1800_ = v_a_1837_;
v___y_1801_ = v_contextDependent_1831_;
goto v___jp_1797_;
}
else
{
v___y_1798_ = v___x_1844_;
v___y_1799_ = v___x_1843_;
v___y_1800_ = v_a_1837_;
v___y_1801_ = v_contextDependent_1828_;
goto v___jp_1797_;
}
}
v___jp_1845_:
{
if (lean_obj_tag(v___y_1846_) == 0)
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___y_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___y_1846_, 1);
v_a_1837_ = v_a_1847_;
goto v___jp_1836_;
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1835_);
lean_dec(v_a_1833_);
lean_dec_ref(v_proof_1830_);
lean_dec_ref(v_e_x27_1829_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
v_a_1848_ = lean_ctor_get(v___y_1846_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___y_1846_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___y_1846_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_proof_1830_);
lean_dec_ref(v_e_x27_1829_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_a_1867_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1834_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1834_);
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
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_proof_1830_);
lean_dec_ref(v_e_x27_1829_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_a_1875_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1832_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1832_);
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
}
else
{
lean_del_object(v___x_1818_);
if (lean_obj_tag(v_a_1816_) == 0)
{
lean_object* v_e_x27_1883_; lean_object* v_proof_1884_; uint8_t v_contextDependent_1885_; uint8_t v_contextDependent_1886_; lean_object* v___x_1887_; 
v_e_x27_1883_ = lean_ctor_get(v_a_1813_, 0);
lean_inc_ref(v_e_x27_1883_);
v_proof_1884_ = lean_ctor_get(v_a_1813_, 1);
lean_inc_ref(v_proof_1884_);
v_contextDependent_1885_ = lean_ctor_get_uint8(v_a_1813_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1813_, 2);
v_contextDependent_1886_ = lean_ctor_get_uint8(v_a_1816_, 1);
lean_dec_ref_known(v_a_1816_, 0);
lean_inc_ref(v_p_1811_);
v___x_1887_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1811_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
lean_inc_ref(v_q_1814_);
v___x_1889_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1814_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v_a_1892_; lean_object* v___y_1901_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
if (lean_obj_tag(v_e_1779_) == 7)
{
lean_object* v_binderName_1911_; lean_object* v_binderType_1912_; lean_object* v_body_1913_; uint8_t v_binderInfo_1914_; uint8_t v___y_1916_; uint8_t v___x_1918_; 
v_binderName_1911_ = lean_ctor_get(v_e_1779_, 0);
v_binderType_1912_ = lean_ctor_get(v_e_1779_, 1);
v_body_1913_ = lean_ctor_get(v_e_1779_, 2);
v_binderInfo_1914_ = lean_ctor_get_uint8(v_e_1779_, sizeof(void*)*3 + 8);
v___x_1918_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1912_, v_e_x27_1883_);
if (v___x_1918_ == 0)
{
v___y_1916_ = v___x_1918_;
goto v___jp_1915_;
}
else
{
uint8_t v___x_1919_; 
v___x_1919_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1913_, v_q_1814_);
v___y_1916_ = v___x_1919_;
goto v___jp_1915_;
}
v___jp_1915_:
{
if (v___y_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_inc(v_binderName_1911_);
lean_dec_ref_known(v_e_1779_, 3);
lean_inc_ref(v_q_1814_);
lean_inc_ref(v_e_x27_1883_);
v___x_1917_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1911_, v_binderInfo_1914_, v_e_x27_1883_, v_q_1814_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
v___y_1901_ = v___x_1917_;
goto v___jp_1900_;
}
else
{
v_a_1892_ = v_e_1779_;
goto v___jp_1891_;
}
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v_e_1779_);
v___x_1920_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1921_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1920_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
v___y_1901_ = v___x_1921_;
goto v___jp_1900_;
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1893_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__7));
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_a_1890_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1888_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l_Lean_mkConst(v___x_1893_, v___x_1896_);
v___x_1898_ = l_Lean_mkApp4(v___x_1897_, v_p_1811_, v_e_x27_1883_, v_q_1814_, v_proof_1884_);
v___x_1899_ = 0;
if (v_contextDependent_1885_ == 0)
{
v___y_1791_ = v_a_1892_;
v___y_1792_ = v___x_1899_;
v___y_1793_ = v___x_1898_;
v___y_1794_ = v_contextDependent_1886_;
goto v___jp_1790_;
}
else
{
v___y_1791_ = v_a_1892_;
v___y_1792_ = v___x_1899_;
v___y_1793_ = v___x_1898_;
v___y_1794_ = v_contextDependent_1885_;
goto v___jp_1790_;
}
}
v___jp_1900_:
{
if (lean_obj_tag(v___y_1901_) == 0)
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___y_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___y_1901_, 1);
v_a_1892_ = v_a_1902_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1890_);
lean_dec(v_a_1888_);
lean_dec_ref(v_proof_1884_);
lean_dec_ref(v_e_x27_1883_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
v_a_1903_ = lean_ctor_get(v___y_1901_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___y_1901_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___y_1901_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___y_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_a_1888_);
lean_dec_ref(v_proof_1884_);
lean_dec_ref(v_e_x27_1883_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_a_1922_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1889_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1889_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_proof_1884_);
lean_dec_ref(v_e_x27_1883_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_a_1930_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1887_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1887_);
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
lean_object* v_e_x27_1938_; lean_object* v_proof_1939_; uint8_t v_contextDependent_1940_; lean_object* v_e_x27_1941_; lean_object* v_proof_1942_; uint8_t v_contextDependent_1943_; lean_object* v___x_1944_; 
v_e_x27_1938_ = lean_ctor_get(v_a_1813_, 0);
lean_inc_ref(v_e_x27_1938_);
v_proof_1939_ = lean_ctor_get(v_a_1813_, 1);
lean_inc_ref(v_proof_1939_);
v_contextDependent_1940_ = lean_ctor_get_uint8(v_a_1813_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1813_, 2);
v_e_x27_1941_ = lean_ctor_get(v_a_1816_, 0);
lean_inc_ref(v_e_x27_1941_);
v_proof_1942_ = lean_ctor_get(v_a_1816_, 1);
lean_inc_ref(v_proof_1942_);
v_contextDependent_1943_ = lean_ctor_get_uint8(v_a_1816_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1816_, 2);
lean_inc_ref(v_p_1811_);
v___x_1944_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1811_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
lean_inc_ref(v_q_1814_);
v___x_1946_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1814_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_a_1949_; lean_object* v___y_1958_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
if (lean_obj_tag(v_e_1779_) == 7)
{
lean_object* v_binderName_1968_; lean_object* v_binderType_1969_; lean_object* v_body_1970_; uint8_t v_binderInfo_1971_; uint8_t v___y_1973_; uint8_t v___x_1975_; 
v_binderName_1968_ = lean_ctor_get(v_e_1779_, 0);
v_binderType_1969_ = lean_ctor_get(v_e_1779_, 1);
v_body_1970_ = lean_ctor_get(v_e_1779_, 2);
v_binderInfo_1971_ = lean_ctor_get_uint8(v_e_1779_, sizeof(void*)*3 + 8);
v___x_1975_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1969_, v_e_x27_1938_);
if (v___x_1975_ == 0)
{
v___y_1973_ = v___x_1975_;
goto v___jp_1972_;
}
else
{
uint8_t v___x_1976_; 
v___x_1976_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1970_, v_e_x27_1941_);
v___y_1973_ = v___x_1976_;
goto v___jp_1972_;
}
v___jp_1972_:
{
if (v___y_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_inc(v_binderName_1968_);
lean_dec_ref_known(v_e_1779_, 3);
lean_inc_ref(v_e_x27_1941_);
lean_inc_ref(v_e_x27_1938_);
v___x_1974_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1968_, v_binderInfo_1971_, v_e_x27_1938_, v_e_x27_1941_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
v___y_1958_ = v___x_1974_;
goto v___jp_1957_;
}
else
{
v_a_1949_ = v_e_1779_;
goto v___jp_1948_;
}
}
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref(v_e_1779_);
v___x_1977_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1978_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1977_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
v___y_1958_ = v___x_1978_;
goto v___jp_1957_;
}
v___jp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1950_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__9));
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1947_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1945_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_mkConst(v___x_1950_, v___x_1953_);
v___x_1955_ = l_Lean_mkApp6(v___x_1954_, v_p_1811_, v_e_x27_1938_, v_q_1814_, v_e_x27_1941_, v_proof_1939_, v_proof_1942_);
v___x_1956_ = 0;
if (v_contextDependent_1940_ == 0)
{
v___y_1805_ = v___x_1955_;
v___y_1806_ = v___x_1956_;
v___y_1807_ = v_a_1949_;
v___y_1808_ = v_contextDependent_1943_;
goto v___jp_1804_;
}
else
{
v___y_1805_ = v___x_1955_;
v___y_1806_ = v___x_1956_;
v___y_1807_ = v_a_1949_;
v___y_1808_ = v_contextDependent_1940_;
goto v___jp_1804_;
}
}
v___jp_1957_:
{
if (lean_obj_tag(v___y_1958_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___y_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___y_1958_, 1);
v_a_1949_ = v_a_1959_;
goto v___jp_1948_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec(v_a_1947_);
lean_dec(v_a_1945_);
lean_dec_ref(v_proof_1942_);
lean_dec_ref(v_e_x27_1941_);
lean_dec_ref(v_proof_1939_);
lean_dec_ref(v_e_x27_1938_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
v_a_1960_ = lean_ctor_get(v___y_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___y_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___y_1958_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___y_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_a_1945_);
lean_dec_ref(v_proof_1942_);
lean_dec_ref(v_e_x27_1941_);
lean_dec_ref(v_proof_1939_);
lean_dec_ref(v_e_x27_1938_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_a_1979_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1946_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1946_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_proof_1942_);
lean_dec_ref(v_e_x27_1941_);
lean_dec_ref(v_proof_1939_);
lean_dec_ref(v_e_x27_1938_);
lean_dec_ref(v_q_1814_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
v_a_1987_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1944_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1944_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1821_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1822_);
v___x_1824_ = v___x_1818_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_dec_ref(v_q_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
return v___x_1815_;
}
}
else
{
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_e_1779_);
return v___x_1812_;
}
v___jp_1790_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1795_, 0, v___y_1791_);
lean_ctor_set(v___x_1795_, 1, v___y_1793_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*2, v___y_1792_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*2 + 1, v___y_1794_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
v___jp_1797_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1802_, 0, v___y_1800_);
lean_ctor_set(v___x_1802_, 1, v___y_1799_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*2, v___y_1798_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*2 + 1, v___y_1801_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
v___jp_1804_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1809_, 0, v___y_1807_);
lean_ctor_set(v___x_1809_, 1, v___y_1805_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*2, v___y_1806_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*2 + 1, v___y_1808_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow___boxed(lean_object* v_e_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Meta_Sym_Simp_simpArrow(v_e_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(lean_object* v_simpBody_2008_, lean_object* v_xs_2009_, lean_object* v_b_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2021_; 
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc_ref(v_b_2010_);
v___x_2021_ = lean_apply_11(v_simpBody_2008_, v_b_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, lean_box(0));
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2112_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2112_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2112_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
if (lean_obj_tag(v_a_2022_) == 0)
{
uint8_t v_contextDependent_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_xs_2009_);
v_contextDependent_2026_ = lean_ctor_get_uint8(v_a_2022_, 1);
lean_dec_ref_known(v_a_2022_, 0);
v___x_2027_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2026_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
else
{
lean_object* v_e_x27_2031_; lean_object* v_proof_2032_; uint8_t v_contextDependent_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2111_; 
lean_del_object(v___x_2024_);
v_e_x27_2031_ = lean_ctor_get(v_a_2022_, 0);
v_proof_2032_ = lean_ctor_get(v_a_2022_, 1);
v_contextDependent_2033_ = lean_ctor_get_uint8(v_a_2022_, sizeof(void*)*2 + 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2035_ = v_a_2022_;
v_isShared_2036_ = v_isSharedCheck_2111_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_proof_2032_);
lean_inc(v_e_x27_2031_);
lean_dec(v_a_2022_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2111_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
uint8_t v___x_2037_; uint8_t v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = 0;
v___x_2038_ = 1;
v___x_2039_ = 1;
v___x_2040_ = l_Lean_Meta_mkLambdaFVars(v_xs_2009_, v_proof_2032_, v___x_2037_, v___x_2038_, v___x_2037_, v___x_2038_, v___x_2039_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
lean_inc_ref(v_e_x27_2031_);
v___x_2042_ = l_Lean_Meta_mkForallFVars(v_xs_2009_, v_e_x27_2031_, v___x_2037_, v___x_2038_, v___x_2038_, v___x_2039_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = l_Lean_Meta_Sym_shareCommon(v_a_2043_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
lean_inc_ref(v_xs_2009_);
v___x_2046_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_2009_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_Meta_mkLambdaFVars(v_xs_2009_, v_b_2010_, v___x_2037_, v___x_2038_, v___x_2037_, v___x_2038_, v___x_2039_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = l_Lean_Meta_mkLambdaFVars(v_xs_2009_, v_e_x27_2031_, v___x_2037_, v___x_2038_, v___x_2037_, v___x_2038_, v___x_2039_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec_ref(v_xs_2009_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2062_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = l_Lean_mkApp3(v_a_2047_, v_a_2049_, v_a_2051_, v_a_2041_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v___x_2055_);
lean_ctor_set(v___x_2035_, 0, v_a_2045_);
v___x_2057_ = v___x_2035_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2045_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2055_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, sizeof(void*)*2 + 1, v_contextDependent_2033_);
v___x_2057_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2059_; 
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*2, v___x_2037_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2057_);
v___x_2059_ = v___x_2053_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2049_);
lean_dec(v_a_2047_);
lean_dec(v_a_2045_);
lean_dec(v_a_2041_);
lean_del_object(v___x_2035_);
v_a_2063_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2050_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2050_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_a_2047_);
lean_dec(v_a_2045_);
lean_dec(v_a_2041_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_x27_2031_);
lean_dec_ref(v_xs_2009_);
v_a_2071_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2048_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2048_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_a_2045_);
lean_dec(v_a_2041_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_x27_2031_);
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_xs_2009_);
v_a_2079_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2046_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2046_);
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
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2041_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_x27_2031_);
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_xs_2009_);
v_a_2087_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2044_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2044_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2041_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_x27_2031_);
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_xs_2009_);
v_a_2095_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2042_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2042_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
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
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_x27_2031_);
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_xs_2009_);
v_a_2103_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2040_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2040_);
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
}
}
}
}
else
{
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_xs_2009_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main___boxed(lean_object* v_simpBody_2113_, lean_object* v_xs_2114_, lean_object* v_b_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2113_, v_xs_2114_, v_b_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(lean_object* v_e_2127_, lean_object* v_n_2128_){
_start:
{
if (lean_obj_tag(v_e_2127_) == 7)
{
lean_object* v_body_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_body_2129_ = lean_ctor_get(v_e_2127_, 2);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_expr_has_loose_bvar(v_body_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
return v_n_2128_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = lean_nat_add(v_n_2128_, v___x_2132_);
lean_dec(v_n_2128_);
v_e_2127_ = v_body_2129_;
v_n_2128_ = v___x_2133_;
goto _start;
}
}
else
{
return v_n_2128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize___boxed(lean_object* v_e_2135_, lean_object* v_n_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v_e_2135_, v_n_2136_);
lean_dec_ref(v_e_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(lean_object* v_k_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v_b_2144_, lean_object* v_c_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
lean_inc(v___y_2149_);
lean_inc_ref(v___y_2148_);
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
lean_inc(v___y_2143_);
lean_inc_ref(v___y_2142_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
v___x_2151_ = lean_apply_12(v_k_2138_, v_b_2144_, v_c_2145_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, lean_box(0));
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v_b_2158_, lean_object* v_c_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(v_k_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v_b_2158_, v_c_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(lean_object* v_type_2166_, lean_object* v_maxFVars_x3f_2167_, lean_object* v_k_2168_, uint8_t v_cleanupAnnotations_2169_, uint8_t v_whnfType_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___f_2181_; lean_object* v___x_2182_; 
lean_inc(v___y_2175_);
lean_inc_ref(v___y_2174_);
lean_inc(v___y_2173_);
lean_inc_ref(v___y_2172_);
lean_inc(v___y_2171_);
v___f_2181_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2181_, 0, v_k_2168_);
lean_closure_set(v___f_2181_, 1, v___y_2171_);
lean_closure_set(v___f_2181_, 2, v___y_2172_);
lean_closure_set(v___f_2181_, 3, v___y_2173_);
lean_closure_set(v___f_2181_, 4, v___y_2174_);
lean_closure_set(v___f_2181_, 5, v___y_2175_);
v___x_2182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2166_, v_maxFVars_x3f_2167_, v___f_2181_, v_cleanupAnnotations_2169_, v_whnfType_2170_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
if (lean_obj_tag(v___x_2182_) == 0)
{
return v___x_2182_;
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___boxed(lean_object* v_type_2191_, lean_object* v_maxFVars_x3f_2192_, lean_object* v_k_2193_, lean_object* v_cleanupAnnotations_2194_, lean_object* v_whnfType_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2206_; uint8_t v_whnfType_boxed_2207_; lean_object* v_res_2208_; 
v_cleanupAnnotations_boxed_2206_ = lean_unbox(v_cleanupAnnotations_2194_);
v_whnfType_boxed_2207_ = lean_unbox(v_whnfType_2195_);
v_res_2208_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2191_, v_maxFVars_x3f_2192_, v_k_2193_, v_cleanupAnnotations_boxed_2206_, v_whnfType_boxed_2207_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(lean_object* v_00_u03b1_2209_, lean_object* v_type_2210_, lean_object* v_maxFVars_x3f_2211_, lean_object* v_k_2212_, uint8_t v_cleanupAnnotations_2213_, uint8_t v_whnfType_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2210_, v_maxFVars_x3f_2211_, v_k_2212_, v_cleanupAnnotations_2213_, v_whnfType_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_type_2227_, lean_object* v_maxFVars_x3f_2228_, lean_object* v_k_2229_, lean_object* v_cleanupAnnotations_2230_, lean_object* v_whnfType_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2242_; uint8_t v_whnfType_boxed_2243_; lean_object* v_res_2244_; 
v_cleanupAnnotations_boxed_2242_ = lean_unbox(v_cleanupAnnotations_2230_);
v_whnfType_boxed_2243_ = lean_unbox(v_whnfType_2231_);
v_res_2244_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(v_00_u03b1_2226_, v_type_2227_, v_maxFVars_x3f_2228_, v_k_2229_, v_cleanupAnnotations_boxed_2242_, v_whnfType_boxed_2243_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(lean_object* v___y_2245_, lean_object* v_transientCache_2246_, lean_object* v_funext_2247_, lean_object* v_a_x3f_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v_numSteps_2251_; lean_object* v_persistentCache_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2262_; 
v___x_2250_ = lean_st_ref_take(v___y_2245_);
v_numSteps_2251_ = lean_ctor_get(v___x_2250_, 0);
v_persistentCache_2252_ = lean_ctor_get(v___x_2250_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; lean_object* v_unused_2264_; 
v_unused_2263_ = lean_ctor_get(v___x_2250_, 3);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v___x_2250_, 2);
lean_dec(v_unused_2264_);
v___x_2254_ = v___x_2250_;
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_persistentCache_2252_);
lean_inc(v_numSteps_2251_);
lean_dec(v___x_2250_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 3, v_funext_2247_);
lean_ctor_set(v___x_2254_, 2, v_transientCache_2246_);
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_numSteps_2251_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_persistentCache_2252_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_transientCache_2246_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_funext_2247_);
v___x_2257_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_st_ref_set(v___y_2245_, v___x_2257_);
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0___boxed(lean_object* v___y_2265_, lean_object* v_transientCache_2266_, lean_object* v_funext_2267_, lean_object* v_a_x3f_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2265_, v_transientCache_2266_, v_funext_2267_, v_a_x3f_2268_);
lean_dec(v_a_x3f_2268_);
lean_dec(v___y_2265_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(lean_object* v_simpBody_2271_, lean_object* v_xs_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v_transientCache_2286_; lean_object* v_funext_2287_; lean_object* v_a_2289_; lean_object* v___x_2300_; 
v___x_2284_ = lean_st_ref_get(v___y_2276_);
v___x_2285_ = lean_st_ref_get(v___y_2276_);
v_transientCache_2286_ = lean_ctor_get(v___x_2284_, 2);
lean_inc_ref(v_transientCache_2286_);
lean_dec(v___x_2284_);
v_funext_2287_ = lean_ctor_get(v___x_2285_, 3);
lean_inc_ref(v_funext_2287_);
lean_dec(v___x_2285_);
v___x_2300_ = l_Lean_Meta_Sym_shareCommon(v_b_2273_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2271_, v_xs_2272_, v_a_2301_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2319_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2319_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2319_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
lean_inc(v_a_2303_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set_tag(v___x_2305_, 1);
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v___x_2309_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2276_, v_transientCache_2286_, v_funext_2287_, v___x_2308_);
lean_dec_ref(v___x_2308_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2309_, 0);
lean_dec(v_unused_2317_);
v___x_2311_ = v___x_2309_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_dec(v___x_2309_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v_a_2303_);
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2303_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
else
{
lean_object* v_a_2320_; 
v_a_2320_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2302_, 1);
v_a_2289_ = v_a_2320_;
goto v___jp_2288_;
}
}
else
{
lean_object* v_a_2321_; 
lean_dec_ref(v_xs_2272_);
lean_dec_ref(v_simpBody_2271_);
v_a_2321_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2300_, 1);
v_a_2289_ = v_a_2321_;
goto v___jp_2288_;
}
v___jp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2276_, v_transientCache_2286_, v_funext_2287_, v___x_2290_);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v___x_2291_, 0);
lean_dec(v_unused_2299_);
v___x_2293_ = v___x_2291_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v___x_2291_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set_tag(v___x_2293_, 1);
lean_ctor_set(v___x_2293_, 0, v_a_2289_);
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2289_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed(lean_object* v_simpBody_2322_, lean_object* v_xs_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(v_simpBody_2322_, v_xs_2323_, v_b_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object* v_simpArrow_2336_, lean_object* v_simpBody_2337_, lean_object* v_e_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Lean_Expr_isArrow(v_e_2338_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec_ref(v_simpArrow_2336_);
lean_inc_ref(v_e_2338_);
v___x_2350_ = l_Lean_Meta_isProp(v_e_2338_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2368_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2368_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2368_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_unbox(v_a_2351_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; uint8_t v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2360_; 
lean_dec_ref(v_e_2338_);
lean_dec_ref(v_simpBody_2337_);
v___x_2356_ = lean_alloc_ctor(0, 0, 2);
v___x_2357_ = lean_unbox(v_a_2351_);
lean_ctor_set_uint8(v___x_2356_, 0, v___x_2357_);
v___x_2358_ = lean_unbox(v_a_2351_);
lean_dec(v_a_2351_);
lean_ctor_set_uint8(v___x_2356_, 1, v___x_2358_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2356_);
v___x_2360_ = v___x_2353_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2356_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
else
{
lean_object* v___f_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_del_object(v___x_2353_);
lean_dec(v_a_2351_);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed), 13, 1);
lean_closure_set(v___f_2362_, 0, v_simpBody_2337_);
v___x_2363_ = l_Lean_Expr_bindingBody_x21(v_e_2338_);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v___x_2363_, v___x_2364_);
lean_dec_ref(v___x_2363_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_e_2338_, v___x_2366_, v___f_2362_, v___x_2349_, v___x_2349_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_e_2338_);
lean_dec_ref(v_simpBody_2337_);
v_a_2369_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2350_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2350_);
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
else
{
lean_object* v___x_2377_; 
lean_dec_ref(v_simpBody_2337_);
lean_inc(v_a_2347_);
lean_inc_ref(v_a_2346_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
lean_inc(v_a_2339_);
v___x_2377_ = lean_apply_11(v_simpArrow_2336_, v_e_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, lean_box(0));
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object* v_simpArrow_2378_, lean_object* v_simpBody_2379_, lean_object* v_e_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v_simpArrow_2378_, v_simpBody_2379_, v_e_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object* v_e_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__0));
v___x_2406_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__1));
v___x_2407_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v___x_2405_, v___x_2406_, v_e_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object* v_e_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
return v_res_2419_;
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
