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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 72, 118, 56, 86, 132, 84, 122)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "arrow_congr_right"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 119, 110, 93, 174, 252, 11, 102)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrow_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value),LEAN_SCALAR_PTR_LITERAL(253, 60, 249, 93, 169, 23, 87, 100)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_true_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value),LEAN_SCALAR_PTR_LITERAL(26, 244, 117, 192, 201, 44, 53, 165)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value),LEAN_SCALAR_PTR_LITERAL(166, 43, 230, 22, 134, 52, 48, 206)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "true_arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value),LEAN_SCALAR_PTR_LITERAL(6, 117, 111, 18, 228, 157, 82, 38)}};
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "true_arrow"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value),LEAN_SCALAR_PTR_LITERAL(167, 3, 129, 158, 41, 225, 71, 211)}};
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
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(lean_object* v___x_9_, lean_object* v_a_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v_xs_13_, lean_object* v___x_14_, lean_object* v_a_15_, lean_object* v___x_16_, lean_object* v_a_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_prop_20_, uint8_t v___x_21_, uint8_t v___x_22_, uint8_t v___x_23_, lean_object* v___x_24_, lean_object* v_p_25_, lean_object* v_q_26_, lean_object* v_h_27_, lean_object* v___x_28_, lean_object* v___x_29_, lean_object* v___x_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v_p_x27_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
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
lean_object* v_a_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_57_, 1);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1));
lean_inc_ref(v___x_9_);
v___x_60_ = l_Lean_Name_mkStr2(v___x_9_, v___x_59_);
lean_inc_n(v___x_24_, 3);
v___x_61_ = l_Lean_mkConst(v___x_60_, v___x_24_);
lean_inc_ref(v_h_27_);
lean_inc_ref_n(v_q_26_, 2);
lean_inc_ref_n(v_p_25_, 2);
lean_inc_ref_n(v_a_17_, 2);
lean_inc_ref_n(v_a_15_, 4);
v___x_62_ = l_Lean_mkApp5(v___x_61_, v_a_15_, v_a_17_, v_p_25_, v_q_26_, v_h_27_);
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2));
v___x_64_ = l_Lean_Name_mkStr2(v___x_9_, v___x_63_);
v___x_65_ = l_Lean_mkConst(v___x_64_, v___x_24_);
lean_inc_ref(v___x_65_);
v___x_66_ = l_Lean_mkApp3(v___x_65_, v_a_15_, v_a_17_, v_p_25_);
v___x_67_ = l_Lean_mkApp3(v___x_65_, v_a_15_, v_a_17_, v_q_26_);
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4));
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v_a_10_);
lean_ctor_set(v___x_69_, 1, v___x_24_);
v___x_70_ = l_Lean_mkConst(v___x_68_, v___x_69_);
v___x_71_ = l_Lean_mkApp6(v___x_70_, v___x_28_, v_a_15_, v___x_66_, v___x_67_, v_a_58_, v___x_62_);
v___x_72_ = l_Lean_Meta_mkForallFVars(v_xs_13_, v___x_29_, v___x_21_, v___x_22_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l_Lean_Meta_mkForallFVars(v_xs_13_, v___x_30_, v___x_21_, v___x_22_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
lean_inc_ref(v_q_26_);
v___x_76_ = lean_array_push(v___x_54_, v_q_26_);
lean_inc(v_a_73_);
lean_inc_ref(v_prop_20_);
v___x_77_ = l_Lean_mkApp3(v___x_31_, v_prop_20_, v_a_73_, v_a_75_);
v___x_78_ = l_Lean_Meta_mkLambdaFVars(v___x_76_, v___x_77_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec_ref(v___x_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5));
lean_inc_ref(v___x_32_);
v___x_81_ = l_Lean_Name_mkStr2(v___x_32_, v___x_80_);
v___x_82_ = l_Lean_mkConst(v___x_81_, v___x_11_);
v___x_83_ = l_Lean_mkAppB(v___x_82_, v_prop_20_, v_a_73_);
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6));
v___x_85_ = l_Lean_Name_mkStr2(v___x_32_, v___x_84_);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_33_);
lean_ctor_set(v___x_86_, 1, v___x_24_);
v___x_87_ = l_Lean_mkConst(v___x_85_, v___x_86_);
lean_inc_ref(v_q_26_);
lean_inc_ref(v_p_25_);
v___x_88_ = l_Lean_mkApp6(v___x_87_, v_a_15_, v_p_25_, v_a_79_, v___x_83_, v_q_26_, v___x_71_);
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
lean_dec(v_a_73_);
lean_dec_ref(v___x_71_);
lean_dec(v___x_33_);
lean_dec_ref(v___x_32_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_q_26_);
lean_dec_ref(v_p_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_prop_20_);
lean_dec_ref(v_a_15_);
lean_dec(v___x_11_);
return v___x_78_;
}
}
else
{
lean_dec(v_a_73_);
lean_dec_ref(v___x_71_);
lean_dec_ref(v___x_54_);
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
return v___x_74_;
}
}
else
{
lean_dec_ref(v___x_71_);
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
lean_dec_ref(v_a_15_);
lean_dec(v___x_11_);
return v___x_72_;
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_9_ = stack[0].m_obj;
lean_object* v_a_10_ = stack[1].m_obj;
lean_object* v___x_11_ = stack[2].m_obj;
lean_object* v___x_12_ = stack[3].m_obj;
lean_object* v_xs_13_ = stack[4].m_obj;
lean_object* v___x_14_ = stack[5].m_obj;
lean_object* v_a_15_ = stack[6].m_obj;
lean_object* v___x_16_ = stack[7].m_obj;
lean_object* v_a_17_ = stack[8].m_obj;
lean_object* v___x_18_ = stack[9].m_obj;
lean_object* v___x_19_ = stack[10].m_obj;
lean_object* v_prop_20_ = stack[11].m_obj;
uint8_t v___x_21_ = stack[12].m_num;
uint8_t v___x_22_ = stack[13].m_num;
uint8_t v___x_23_ = stack[14].m_num;
lean_object* v___x_24_ = stack[15].m_obj;
lean_object* v_p_25_ = stack[16].m_obj;
lean_object* v_q_26_ = stack[17].m_obj;
lean_object* v_h_27_ = stack[18].m_obj;
lean_object* v___x_28_ = stack[19].m_obj;
lean_object* v___x_29_ = stack[20].m_obj;
lean_object* v___x_30_ = stack[21].m_obj;
lean_object* v___x_31_ = stack[22].m_obj;
lean_object* v___x_32_ = stack[23].m_obj;
lean_object* v___x_33_ = stack[24].m_obj;
lean_object* v_p_x27_34_ = stack[25].m_obj;
lean_object* v___y_35_ = stack[26].m_obj;
lean_object* v___y_36_ = stack[27].m_obj;
lean_object* v___y_37_ = stack[28].m_obj;
lean_object* v___y_38_ = stack[29].m_obj;
lean_object* v_res_95_;
v_res_95_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(v___x_9_, v_a_10_, v___x_11_, v___x_12_, v_xs_13_, v___x_14_, v_a_15_, v___x_16_, v_a_17_, v___x_18_, v___x_19_, v_prop_20_, v___x_21_, v___x_22_, v___x_23_, v___x_24_, v_p_25_, v_q_26_, v_h_27_, v___x_28_, v___x_29_, v___x_30_, v___x_31_, v___x_32_, v___x_33_, v_p_x27_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed(lean_object** _args){
lean_object* v___x_96_ = _args[0];
lean_object* v_a_97_ = _args[1];
lean_object* v___x_98_ = _args[2];
lean_object* v___x_99_ = _args[3];
lean_object* v_xs_100_ = _args[4];
lean_object* v___x_101_ = _args[5];
lean_object* v_a_102_ = _args[6];
lean_object* v___x_103_ = _args[7];
lean_object* v_a_104_ = _args[8];
lean_object* v___x_105_ = _args[9];
lean_object* v___x_106_ = _args[10];
lean_object* v_prop_107_ = _args[11];
lean_object* v___x_108_ = _args[12];
lean_object* v___x_109_ = _args[13];
lean_object* v___x_110_ = _args[14];
lean_object* v___x_111_ = _args[15];
lean_object* v_p_112_ = _args[16];
lean_object* v_q_113_ = _args[17];
lean_object* v_h_114_ = _args[18];
lean_object* v___x_115_ = _args[19];
lean_object* v___x_116_ = _args[20];
lean_object* v___x_117_ = _args[21];
lean_object* v___x_118_ = _args[22];
lean_object* v___x_119_ = _args[23];
lean_object* v___x_120_ = _args[24];
lean_object* v_p_x27_121_ = _args[25];
lean_object* v___y_122_ = _args[26];
lean_object* v___y_123_ = _args[27];
lean_object* v___y_124_ = _args[28];
lean_object* v___y_125_ = _args[29];
lean_object* v___y_126_ = _args[30];
_start:
{
uint8_t v___x_2438__boxed_127_; uint8_t v___x_2439__boxed_128_; uint8_t v___x_2440__boxed_129_; lean_object* v_res_130_; 
v___x_2438__boxed_127_ = lean_unbox(v___x_108_);
v___x_2439__boxed_128_ = lean_unbox(v___x_109_);
v___x_2440__boxed_129_ = lean_unbox(v___x_110_);
v_res_130_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(v___x_96_, v_a_97_, v___x_98_, v___x_99_, v_xs_100_, v___x_101_, v_a_102_, v___x_103_, v_a_104_, v___x_105_, v___x_106_, v_prop_107_, v___x_2438__boxed_127_, v___x_2439__boxed_128_, v___x_2440__boxed_129_, v___x_111_, v_p_112_, v_q_113_, v_h_114_, v___x_115_, v___x_116_, v___x_117_, v___x_118_, v___x_119_, v___x_120_, v_p_x27_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec_ref(v_xs_100_);
return v_res_130_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(lean_object* v_k_131_, lean_object* v_b_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
v___x_138_ = lean_apply_6(v_k_131_, v_b_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_131_ = stack[0].m_obj;
lean_object* v_b_132_ = stack[1].m_obj;
lean_object* v___y_133_ = stack[2].m_obj;
lean_object* v___y_134_ = stack[3].m_obj;
lean_object* v___y_135_ = stack[4].m_obj;
lean_object* v___y_136_ = stack[5].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(v_k_131_, v_b_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_140_, lean_object* v_b_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(v_k_140_, v_b_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(lean_object* v_name_148_, uint8_t v_bi_149_, lean_object* v_type_150_, lean_object* v_k_151_, uint8_t v_kind_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___f_158_; lean_object* v___x_159_; 
v___f_158_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_158_, 0, v_k_151_);
v___x_159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_148_, v_bi_149_, v_type_150_, v___f_158_, v_kind_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_159_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_159_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_148_ = stack[0].m_obj;
uint8_t v_bi_149_ = stack[1].m_num;
lean_object* v_type_150_ = stack[2].m_obj;
lean_object* v_k_151_ = stack[3].m_obj;
uint8_t v_kind_152_ = stack[4].m_num;
lean_object* v___y_153_ = stack[5].m_obj;
lean_object* v___y_154_ = stack[6].m_obj;
lean_object* v___y_155_ = stack[7].m_obj;
lean_object* v___y_156_ = stack[8].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_148_, v_bi_149_, v_type_150_, v_k_151_, v_kind_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___boxed(lean_object* v_name_177_, lean_object* v_bi_178_, lean_object* v_type_179_, lean_object* v_k_180_, lean_object* v_kind_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v_bi_boxed_187_; uint8_t v_kind_boxed_188_; lean_object* v_res_189_; 
v_bi_boxed_187_ = lean_unbox(v_bi_178_);
v_kind_boxed_188_ = lean_unbox(v_kind_181_);
v_res_189_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_177_, v_bi_boxed_187_, v_type_179_, v_k_180_, v_kind_boxed_188_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_189_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(lean_object* v_name_190_, lean_object* v_type_191_, lean_object* v_k_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = 0;
v___x_199_ = 0;
v___x_200_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_190_, v___x_198_, v_type_191_, v_k_192_, v___x_199_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
return v___x_200_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_190_ = stack[0].m_obj;
lean_object* v_type_191_ = stack[1].m_obj;
lean_object* v_k_192_ = stack[2].m_obj;
lean_object* v___y_193_ = stack[3].m_obj;
lean_object* v___y_194_ = stack[4].m_obj;
lean_object* v___y_195_ = stack[5].m_obj;
lean_object* v___y_196_ = stack[6].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_190_, v_type_191_, v_k_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg___boxed(lean_object* v_name_202_, lean_object* v_type_203_, lean_object* v_k_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_202_, v_type_203_, v_k_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_210_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(lean_object* v_xs_217_, lean_object* v___x_218_, uint8_t v___x_219_, uint8_t v___x_220_, uint8_t v___x_221_, lean_object* v_p_222_, lean_object* v_q_223_, lean_object* v_a_224_, lean_object* v___x_225_, lean_object* v_a_226_, lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v_prop_233_, lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v___x_236_, lean_object* v___x_237_, lean_object* v___x_238_, lean_object* v_h_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_mkForallFVars(v_xs_217_, v___x_218_, v___x_219_, v___x_220_, v___x_220_, v___x_221_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
v___x_247_ = lean_unsigned_to_nat(2u);
v___x_248_ = lean_mk_empty_array_with_capacity(v___x_247_);
lean_inc_ref(v_p_222_);
v___x_249_ = lean_array_push(v___x_248_, v_p_222_);
lean_inc_ref(v_q_223_);
v___x_250_ = lean_array_push(v___x_249_, v_q_223_);
v___x_251_ = l_Lean_Meta_mkLambdaFVars(v___x_250_, v_a_246_, v___x_219_, v___x_220_, v___x_219_, v___x_220_, v___x_221_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec_ref(v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_n(v_a_252_, 2);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0));
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1));
lean_inc(v_a_224_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v_a_224_);
lean_ctor_set(v___x_255_, 1, v___x_225_);
lean_inc_ref(v___x_255_);
v___x_256_ = l_Lean_mkConst(v___x_254_, v___x_255_);
lean_inc_ref(v_a_226_);
v___x_257_ = l_Lean_mkAppB(v___x_256_, v_a_226_, v_a_252_);
v___x_258_ = lean_box(v___x_219_);
v___x_259_ = lean_box(v___x_220_);
v___x_260_ = lean_box(v___x_221_);
lean_inc_ref(v___x_257_);
v___f_261_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed), 31, 25);
lean_closure_set(v___f_261_, 0, v___x_253_);
lean_closure_set(v___f_261_, 1, v_a_224_);
lean_closure_set(v___f_261_, 2, v___x_227_);
lean_closure_set(v___f_261_, 3, v___x_228_);
lean_closure_set(v___f_261_, 4, v_xs_217_);
lean_closure_set(v___f_261_, 5, v___x_229_);
lean_closure_set(v___f_261_, 6, v_a_226_);
lean_closure_set(v___f_261_, 7, v___x_230_);
lean_closure_set(v___f_261_, 8, v_a_252_);
lean_closure_set(v___f_261_, 9, v___x_231_);
lean_closure_set(v___f_261_, 10, v___x_232_);
lean_closure_set(v___f_261_, 11, v_prop_233_);
lean_closure_set(v___f_261_, 12, v___x_258_);
lean_closure_set(v___f_261_, 13, v___x_259_);
lean_closure_set(v___f_261_, 14, v___x_260_);
lean_closure_set(v___f_261_, 15, v___x_255_);
lean_closure_set(v___f_261_, 16, v_p_222_);
lean_closure_set(v___f_261_, 17, v_q_223_);
lean_closure_set(v___f_261_, 18, v_h_239_);
lean_closure_set(v___f_261_, 19, v___x_257_);
lean_closure_set(v___f_261_, 20, v___x_234_);
lean_closure_set(v___f_261_, 21, v___x_235_);
lean_closure_set(v___f_261_, 22, v___x_236_);
lean_closure_set(v___f_261_, 23, v___x_237_);
lean_closure_set(v___f_261_, 24, v___x_238_);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3));
v___x_263_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_262_, v___x_257_, v___f_261_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
return v___x_263_;
}
else
{
lean_dec_ref(v_h_239_);
lean_dec(v___x_238_);
lean_dec_ref(v___x_237_);
lean_dec_ref(v___x_236_);
lean_dec_ref(v___x_235_);
lean_dec_ref(v___x_234_);
lean_dec_ref(v_prop_233_);
lean_dec(v___x_232_);
lean_dec(v___x_231_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec(v___x_228_);
lean_dec(v___x_227_);
lean_dec_ref(v_a_226_);
lean_dec(v___x_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_q_223_);
lean_dec_ref(v_p_222_);
lean_dec_ref(v_xs_217_);
return v___x_251_;
}
}
else
{
lean_dec_ref(v_h_239_);
lean_dec(v___x_238_);
lean_dec_ref(v___x_237_);
lean_dec_ref(v___x_236_);
lean_dec_ref(v___x_235_);
lean_dec_ref(v___x_234_);
lean_dec_ref(v_prop_233_);
lean_dec(v___x_232_);
lean_dec(v___x_231_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec(v___x_228_);
lean_dec(v___x_227_);
lean_dec_ref(v_a_226_);
lean_dec(v___x_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_q_223_);
lean_dec_ref(v_p_222_);
lean_dec_ref(v_xs_217_);
return v___x_245_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_217_ = stack[0].m_obj;
lean_object* v___x_218_ = stack[1].m_obj;
uint8_t v___x_219_ = stack[2].m_num;
uint8_t v___x_220_ = stack[3].m_num;
uint8_t v___x_221_ = stack[4].m_num;
lean_object* v_p_222_ = stack[5].m_obj;
lean_object* v_q_223_ = stack[6].m_obj;
lean_object* v_a_224_ = stack[7].m_obj;
lean_object* v___x_225_ = stack[8].m_obj;
lean_object* v_a_226_ = stack[9].m_obj;
lean_object* v___x_227_ = stack[10].m_obj;
lean_object* v___x_228_ = stack[11].m_obj;
lean_object* v___x_229_ = stack[12].m_obj;
lean_object* v___x_230_ = stack[13].m_obj;
lean_object* v___x_231_ = stack[14].m_obj;
lean_object* v___x_232_ = stack[15].m_obj;
lean_object* v_prop_233_ = stack[16].m_obj;
lean_object* v___x_234_ = stack[17].m_obj;
lean_object* v___x_235_ = stack[18].m_obj;
lean_object* v___x_236_ = stack[19].m_obj;
lean_object* v___x_237_ = stack[20].m_obj;
lean_object* v___x_238_ = stack[21].m_obj;
lean_object* v_h_239_ = stack[22].m_obj;
lean_object* v___y_240_ = stack[23].m_obj;
lean_object* v___y_241_ = stack[24].m_obj;
lean_object* v___y_242_ = stack[25].m_obj;
lean_object* v___y_243_ = stack[26].m_obj;
lean_object* v_res_264_;
v_res_264_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(v_xs_217_, v___x_218_, v___x_219_, v___x_220_, v___x_221_, v_p_222_, v_q_223_, v_a_224_, v___x_225_, v_a_226_, v___x_227_, v___x_228_, v___x_229_, v___x_230_, v___x_231_, v___x_232_, v_prop_233_, v___x_234_, v___x_235_, v___x_236_, v___x_237_, v___x_238_, v_h_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed(lean_object** _args){
lean_object* v_xs_265_ = _args[0];
lean_object* v___x_266_ = _args[1];
lean_object* v___x_267_ = _args[2];
lean_object* v___x_268_ = _args[3];
lean_object* v___x_269_ = _args[4];
lean_object* v_p_270_ = _args[5];
lean_object* v_q_271_ = _args[6];
lean_object* v_a_272_ = _args[7];
lean_object* v___x_273_ = _args[8];
lean_object* v_a_274_ = _args[9];
lean_object* v___x_275_ = _args[10];
lean_object* v___x_276_ = _args[11];
lean_object* v___x_277_ = _args[12];
lean_object* v___x_278_ = _args[13];
lean_object* v___x_279_ = _args[14];
lean_object* v___x_280_ = _args[15];
lean_object* v_prop_281_ = _args[16];
lean_object* v___x_282_ = _args[17];
lean_object* v___x_283_ = _args[18];
lean_object* v___x_284_ = _args[19];
lean_object* v___x_285_ = _args[20];
lean_object* v___x_286_ = _args[21];
lean_object* v_h_287_ = _args[22];
lean_object* v___y_288_ = _args[23];
lean_object* v___y_289_ = _args[24];
lean_object* v___y_290_ = _args[25];
lean_object* v___y_291_ = _args[26];
lean_object* v___y_292_ = _args[27];
_start:
{
uint8_t v___x_2892__boxed_293_; uint8_t v___x_2893__boxed_294_; uint8_t v___x_2894__boxed_295_; lean_object* v_res_296_; 
v___x_2892__boxed_293_ = lean_unbox(v___x_267_);
v___x_2893__boxed_294_ = lean_unbox(v___x_268_);
v___x_2894__boxed_295_ = lean_unbox(v___x_269_);
v_res_296_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(v_xs_265_, v___x_266_, v___x_2892__boxed_293_, v___x_2893__boxed_294_, v___x_2894__boxed_295_, v_p_270_, v_q_271_, v_a_272_, v___x_273_, v_a_274_, v___x_275_, v___x_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, v_prop_281_, v___x_282_, v___x_283_, v___x_284_, v___x_285_, v___x_286_, v_h_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = l_Lean_Level_ofNat(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2);
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1));
v___x_307_ = l_Lean_mkConst(v___x_306_, v___x_305_);
return v___x_307_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(lean_object* v_p_311_, lean_object* v_xs_312_, lean_object* v_prop_313_, uint8_t v___x_314_, uint8_t v___x_315_, uint8_t v___x_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v___x_319_, lean_object* v___x_320_, lean_object* v___x_321_, lean_object* v___x_322_, lean_object* v_q_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0));
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_box(0);
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4);
lean_inc_ref(v_p_311_);
v___x_334_ = l_Lean_mkAppN(v_p_311_, v_xs_312_);
lean_inc_ref(v_q_323_);
v___x_335_ = l_Lean_mkAppN(v_q_323_, v_xs_312_);
lean_inc_ref(v___x_335_);
lean_inc_ref(v___x_334_);
lean_inc_ref(v_prop_313_);
v___x_336_ = l_Lean_mkApp3(v___x_333_, v_prop_313_, v___x_334_, v___x_335_);
lean_inc_ref(v___x_336_);
v___x_337_ = l_Lean_Meta_mkForallFVars(v_xs_312_, v___x_336_, v___x_314_, v___x_315_, v___x_315_, v___x_316_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___x_344_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6));
v___x_340_ = lean_box(v___x_314_);
v___x_341_ = lean_box(v___x_315_);
v___x_342_ = lean_box(v___x_316_);
v___f_343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed), 28, 22);
lean_closure_set(v___f_343_, 0, v_xs_312_);
lean_closure_set(v___f_343_, 1, v___x_336_);
lean_closure_set(v___f_343_, 2, v___x_340_);
lean_closure_set(v___f_343_, 3, v___x_341_);
lean_closure_set(v___f_343_, 4, v___x_342_);
lean_closure_set(v___f_343_, 5, v_p_311_);
lean_closure_set(v___f_343_, 6, v_q_323_);
lean_closure_set(v___f_343_, 7, v_a_317_);
lean_closure_set(v___f_343_, 8, v___x_331_);
lean_closure_set(v___f_343_, 9, v_a_318_);
lean_closure_set(v___f_343_, 10, v___x_332_);
lean_closure_set(v___f_343_, 11, v___x_319_);
lean_closure_set(v___f_343_, 12, v___x_320_);
lean_closure_set(v___f_343_, 13, v___x_330_);
lean_closure_set(v___f_343_, 14, v___x_339_);
lean_closure_set(v___f_343_, 15, v___x_321_);
lean_closure_set(v___f_343_, 16, v_prop_313_);
lean_closure_set(v___f_343_, 17, v___x_334_);
lean_closure_set(v___f_343_, 18, v___x_335_);
lean_closure_set(v___f_343_, 19, v___x_333_);
lean_closure_set(v___f_343_, 20, v___x_329_);
lean_closure_set(v___f_343_, 21, v___x_322_);
v___x_344_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_339_, v_a_338_, v___f_343_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
return v___x_344_;
}
else
{
lean_dec_ref(v___x_336_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_q_323_);
lean_dec(v___x_322_);
lean_dec(v___x_321_);
lean_dec(v___x_320_);
lean_dec(v___x_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_prop_313_);
lean_dec_ref(v_xs_312_);
lean_dec_ref(v_p_311_);
return v___x_337_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_311_ = stack[0].m_obj;
lean_object* v_xs_312_ = stack[1].m_obj;
lean_object* v_prop_313_ = stack[2].m_obj;
uint8_t v___x_314_ = stack[3].m_num;
uint8_t v___x_315_ = stack[4].m_num;
uint8_t v___x_316_ = stack[5].m_num;
lean_object* v_a_317_ = stack[6].m_obj;
lean_object* v_a_318_ = stack[7].m_obj;
lean_object* v___x_319_ = stack[8].m_obj;
lean_object* v___x_320_ = stack[9].m_obj;
lean_object* v___x_321_ = stack[10].m_obj;
lean_object* v___x_322_ = stack[11].m_obj;
lean_object* v_q_323_ = stack[12].m_obj;
lean_object* v___y_324_ = stack[13].m_obj;
lean_object* v___y_325_ = stack[14].m_obj;
lean_object* v___y_326_ = stack[15].m_obj;
lean_object* v___y_327_ = stack[16].m_obj;
lean_object* v_res_345_;
v_res_345_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(v_p_311_, v_xs_312_, v_prop_313_, v___x_314_, v___x_315_, v___x_316_, v_a_317_, v_a_318_, v___x_319_, v___x_320_, v___x_321_, v___x_322_, v_q_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed(lean_object** _args){
lean_object* v_p_346_ = _args[0];
lean_object* v_xs_347_ = _args[1];
lean_object* v_prop_348_ = _args[2];
lean_object* v___x_349_ = _args[3];
lean_object* v___x_350_ = _args[4];
lean_object* v___x_351_ = _args[5];
lean_object* v_a_352_ = _args[6];
lean_object* v_a_353_ = _args[7];
lean_object* v___x_354_ = _args[8];
lean_object* v___x_355_ = _args[9];
lean_object* v___x_356_ = _args[10];
lean_object* v___x_357_ = _args[11];
lean_object* v_q_358_ = _args[12];
lean_object* v___y_359_ = _args[13];
lean_object* v___y_360_ = _args[14];
lean_object* v___y_361_ = _args[15];
lean_object* v___y_362_ = _args[16];
lean_object* v___y_363_ = _args[17];
_start:
{
uint8_t v___x_3105__boxed_364_; uint8_t v___x_3106__boxed_365_; uint8_t v___x_3107__boxed_366_; lean_object* v_res_367_; 
v___x_3105__boxed_364_ = lean_unbox(v___x_349_);
v___x_3106__boxed_365_ = lean_unbox(v___x_350_);
v___x_3107__boxed_366_ = lean_unbox(v___x_351_);
v_res_367_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(v_p_346_, v_xs_347_, v_prop_348_, v___x_3105__boxed_364_, v___x_3106__boxed_365_, v___x_3107__boxed_366_, v_a_352_, v_a_353_, v___x_354_, v___x_355_, v___x_356_, v___x_357_, v_q_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_367_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(lean_object* v_xs_371_, lean_object* v_prop_372_, uint8_t v___x_373_, uint8_t v___x_374_, uint8_t v___x_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v___x_378_, lean_object* v___x_379_, lean_object* v___x_380_, lean_object* v_p_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___f_391_; lean_object* v___x_392_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1));
v___x_388_ = lean_box(v___x_373_);
v___x_389_ = lean_box(v___x_374_);
v___x_390_ = lean_box(v___x_375_);
lean_inc_ref(v_a_377_);
v___f_391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed), 18, 12);
lean_closure_set(v___f_391_, 0, v_p_381_);
lean_closure_set(v___f_391_, 1, v_xs_371_);
lean_closure_set(v___f_391_, 2, v_prop_372_);
lean_closure_set(v___f_391_, 3, v___x_388_);
lean_closure_set(v___f_391_, 4, v___x_389_);
lean_closure_set(v___f_391_, 5, v___x_390_);
lean_closure_set(v___f_391_, 6, v_a_376_);
lean_closure_set(v___f_391_, 7, v_a_377_);
lean_closure_set(v___f_391_, 8, v___x_378_);
lean_closure_set(v___f_391_, 9, v___x_379_);
lean_closure_set(v___f_391_, 10, v___x_387_);
lean_closure_set(v___f_391_, 11, v___x_380_);
v___x_392_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_387_, v_a_377_, v___f_391_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
return v___x_392_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_371_ = stack[0].m_obj;
lean_object* v_prop_372_ = stack[1].m_obj;
uint8_t v___x_373_ = stack[2].m_num;
uint8_t v___x_374_ = stack[3].m_num;
uint8_t v___x_375_ = stack[4].m_num;
lean_object* v_a_376_ = stack[5].m_obj;
lean_object* v_a_377_ = stack[6].m_obj;
lean_object* v___x_378_ = stack[7].m_obj;
lean_object* v___x_379_ = stack[8].m_obj;
lean_object* v___x_380_ = stack[9].m_obj;
lean_object* v_p_381_ = stack[10].m_obj;
lean_object* v___y_382_ = stack[11].m_obj;
lean_object* v___y_383_ = stack[12].m_obj;
lean_object* v___y_384_ = stack[13].m_obj;
lean_object* v___y_385_ = stack[14].m_obj;
lean_object* v_res_393_;
v_res_393_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(v_xs_371_, v_prop_372_, v___x_373_, v___x_374_, v___x_375_, v_a_376_, v_a_377_, v___x_378_, v___x_379_, v___x_380_, v_p_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed(lean_object* v_xs_394_, lean_object* v_prop_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v___x_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v_p_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v___x_3258__boxed_410_; uint8_t v___x_3259__boxed_411_; uint8_t v___x_3260__boxed_412_; lean_object* v_res_413_; 
v___x_3258__boxed_410_ = lean_unbox(v___x_396_);
v___x_3259__boxed_411_ = lean_unbox(v___x_397_);
v___x_3260__boxed_412_ = lean_unbox(v___x_398_);
v_res_413_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(v_xs_394_, v_prop_395_, v___x_3258__boxed_410_, v___x_3259__boxed_411_, v___x_3260__boxed_412_, v_a_399_, v_a_400_, v___x_401_, v___x_402_, v___x_403_, v_p_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = l_Lean_Level_ofNat(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v_prop_417_; 
v___x_416_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v_prop_417_ = l_Lean_mkSort(v___x_416_);
return v_prop_417_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(lean_object* v_xs_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_prop_429_; uint8_t v___x_430_; uint8_t v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v_prop_429_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1);
v___x_430_ = 0;
v___x_431_ = 1;
v___x_432_ = 1;
v___x_433_ = l_Lean_Meta_mkForallFVars(v_xs_421_, v_prop_429_, v___x_430_, v___x_431_, v___x_431_, v___x_432_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_n(v_a_434_, 2);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = l_Lean_Meta_getLevel(v_a_434_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___f_441_; lean_object* v___x_442_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3));
v___x_438_ = lean_box(v___x_430_);
v___x_439_ = lean_box(v___x_431_);
v___x_440_ = lean_box(v___x_432_);
lean_inc(v_a_434_);
v___f_441_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed), 16, 10);
lean_closure_set(v___f_441_, 0, v_xs_421_);
lean_closure_set(v___f_441_, 1, v_prop_429_);
lean_closure_set(v___f_441_, 2, v___x_438_);
lean_closure_set(v___f_441_, 3, v___x_439_);
lean_closure_set(v___f_441_, 4, v___x_440_);
lean_closure_set(v___f_441_, 5, v_a_436_);
lean_closure_set(v___f_441_, 6, v_a_434_);
lean_closure_set(v___f_441_, 7, v___x_427_);
lean_closure_set(v___f_441_, 8, v___x_437_);
lean_closure_set(v___f_441_, 9, v___x_428_);
v___x_442_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_437_, v_a_434_, v___f_441_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_a_434_);
lean_dec_ref(v_xs_421_);
v_a_443_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_435_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_435_);
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
lean_dec_ref(v_xs_421_);
return v___x_433_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_421_ = stack[0].m_obj;
lean_object* v_a_422_ = stack[1].m_obj;
lean_object* v_a_423_ = stack[2].m_obj;
lean_object* v_a_424_ = stack[3].m_obj;
lean_object* v_a_425_ = stack[4].m_obj;
lean_object* v_res_451_;
v_res_451_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___boxed(lean_object* v_xs_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
return v_res_458_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(lean_object* v_00_u03b1_459_, lean_object* v_name_460_, uint8_t v_bi_461_, lean_object* v_type_462_, lean_object* v_k_463_, uint8_t v_kind_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_460_, v_bi_461_, v_type_462_, v_k_463_, v_kind_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_470_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_460_ = stack[1].m_obj;
uint8_t v_bi_461_ = stack[2].m_num;
lean_object* v_type_462_ = stack[3].m_obj;
lean_object* v_k_463_ = stack[4].m_obj;
uint8_t v_kind_464_ = stack[5].m_num;
lean_object* v___y_465_ = stack[6].m_obj;
lean_object* v___y_466_ = stack[7].m_obj;
lean_object* v___y_467_ = stack[8].m_obj;
lean_object* v___y_468_ = stack[9].m_obj;
lean_object* v_res_471_;
v_res_471_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(lean_box(0), v_name_460_, v_bi_461_, v_type_462_, v_k_463_, v_kind_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
stack->m_obj
 = v_res_471_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_472_, lean_object* v_name_473_, lean_object* v_bi_474_, lean_object* v_type_475_, lean_object* v_k_476_, lean_object* v_kind_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
uint8_t v_bi_boxed_483_; uint8_t v_kind_boxed_484_; lean_object* v_res_485_; 
v_bi_boxed_483_ = lean_unbox(v_bi_474_);
v_kind_boxed_484_ = lean_unbox(v_kind_477_);
v_res_485_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(v_00_u03b1_472_, v_name_473_, v_bi_boxed_483_, v_type_475_, v_k_476_, v_kind_boxed_484_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_485_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(lean_object* v_00_u03b1_486_, lean_object* v_name_487_, lean_object* v_type_488_, lean_object* v_k_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_487_, v_type_488_, v_k_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_487_ = stack[1].m_obj;
lean_object* v_type_488_ = stack[2].m_obj;
lean_object* v_k_489_ = stack[3].m_obj;
lean_object* v___y_490_ = stack[4].m_obj;
lean_object* v___y_491_ = stack[5].m_obj;
lean_object* v___y_492_ = stack[6].m_obj;
lean_object* v___y_493_ = stack[7].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(lean_box(0), v_name_487_, v_type_488_, v_k_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___boxed(lean_object* v_00_u03b1_497_, lean_object* v_name_498_, lean_object* v_type_499_, lean_object* v_k_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(v_00_u03b1_497_, v_name_498_, v_type_499_, v_k_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(lean_object* v_declName_507_, lean_object* v_us_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l_Lean_Expr_const___override(v_declName_507_, v_us_508_);
v___x_512_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_511_, v___y_509_);
return v___x_512_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_507_ = stack[0].m_obj;
lean_object* v_us_508_ = stack[1].m_obj;
lean_object* v___y_509_ = stack[2].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_507_, v_us_508_, v___y_509_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg___boxed(lean_object* v_declName_514_, lean_object* v_us_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_514_, v_us_515_, v___y_516_);
lean_dec(v___y_516_);
return v_res_518_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(lean_object* v_declName_519_, lean_object* v_us_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_519_, v_us_520_, v___y_522_);
return v___x_528_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_519_ = stack[0].m_obj;
lean_object* v_us_520_ = stack[1].m_obj;
lean_object* v___y_521_ = stack[2].m_obj;
lean_object* v___y_522_ = stack[3].m_obj;
lean_object* v___y_523_ = stack[4].m_obj;
lean_object* v___y_524_ = stack[5].m_obj;
lean_object* v___y_525_ = stack[6].m_obj;
lean_object* v___y_526_ = stack[7].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(v_declName_519_, v_us_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___boxed(lean_object* v_declName_530_, lean_object* v_us_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(v_declName_530_, v_us_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_539_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(lean_object* v_f_540_, lean_object* v_a_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___y_550_; lean_object* v___x_553_; uint8_t v_debug_554_; 
v___x_553_ = lean_st_ref_get(v___y_543_);
v_debug_554_ = lean_ctor_get_uint8(v___x_553_, sizeof(void*)*12);
lean_dec(v___x_553_);
if (v_debug_554_ == 0)
{
v___y_550_ = v___y_543_;
goto v___jp_549_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_540_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
lean_dec_ref_known(v___x_555_, 1);
v___x_556_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec_ref_known(v___x_556_, 1);
v___y_550_ = v___y_543_;
goto v___jp_549_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v_a_541_);
lean_dec_ref(v_f_540_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v_a_541_);
lean_dec_ref(v_f_540_);
v_a_565_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_555_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = l_Lean_Expr_app___override(v_f_540_, v_a_541_);
v___x_552_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_551_, v___y_550_);
return v___x_552_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_540_ = stack[0].m_obj;
lean_object* v_a_541_ = stack[1].m_obj;
lean_object* v___y_542_ = stack[2].m_obj;
lean_object* v___y_543_ = stack[3].m_obj;
lean_object* v___y_544_ = stack[4].m_obj;
lean_object* v___y_545_ = stack[5].m_obj;
lean_object* v___y_546_ = stack[6].m_obj;
lean_object* v___y_547_ = stack[7].m_obj;
lean_object* v_res_573_;
v_res_573_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_540_, v_a_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1___boxed(lean_object* v_f_574_, lean_object* v_a_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_574_, v_a_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_583_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(lean_object* v_f_584_, lean_object* v_a_u2081_585_, lean_object* v_a_u2082_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_584_, v_a_u2081_585_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_595_, v_a_u2082_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_596_;
}
else
{
lean_dec_ref(v_a_u2082_586_);
return v___x_594_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_584_ = stack[0].m_obj;
lean_object* v_a_u2081_585_ = stack[1].m_obj;
lean_object* v_a_u2082_586_ = stack[2].m_obj;
lean_object* v___y_587_ = stack[3].m_obj;
lean_object* v___y_588_ = stack[4].m_obj;
lean_object* v___y_589_ = stack[5].m_obj;
lean_object* v___y_590_ = stack[6].m_obj;
lean_object* v___y_591_ = stack[7].m_obj;
lean_object* v___y_592_ = stack[8].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_f_584_, v_a_u2081_585_, v_a_u2082_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1___boxed(lean_object* v_f_598_, lean_object* v_a_u2081_599_, lean_object* v_a_u2082_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_f_598_, v_a_u2081_599_, v_a_u2082_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_608_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(lean_object* v_e_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; 
if (lean_obj_tag(v_e_614_) == 7)
{
lean_object* v_binderName_647_; lean_object* v_binderType_648_; lean_object* v_body_649_; uint8_t v_binderInfo_650_; uint8_t v___x_651_; 
v_binderName_647_ = lean_ctor_get(v_e_614_, 0);
v_binderType_648_ = lean_ctor_get(v_e_614_, 1);
v_body_649_ = lean_ctor_get(v_e_614_, 2);
v_binderInfo_650_ = lean_ctor_get_uint8(v_e_614_, sizeof(void*)*3 + 8);
v___x_651_ = l_Lean_Expr_hasLooseBVars(v_body_649_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_inc_ref(v_body_649_);
lean_inc_ref(v_binderType_648_);
lean_inc(v_binderName_647_);
lean_dec_ref_known(v_e_614_, 3);
v___x_652_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_body_649_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_arrow_654_; lean_object* v_infos_655_; lean_object* v_v_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_707_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v_arrow_654_ = lean_ctor_get(v_a_653_, 0);
v_infos_655_ = lean_ctor_get(v_a_653_, 1);
v_v_656_ = lean_ctor_get(v_a_653_, 2);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_653_);
if (v_isSharedCheck_707_ == 0)
{
v___x_658_ = v_a_653_;
v_isShared_659_ = v_isSharedCheck_707_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_v_656_);
lean_inc(v_infos_655_);
lean_inc(v_arrow_654_);
lean_dec(v_a_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_707_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; 
lean_inc_ref(v_binderType_648_);
v___x_660_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_648_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_n(v_a_661_, 2);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_663_ = lean_box(0);
lean_inc(v_v_656_);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v_v_656_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v_a_661_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v___x_662_, v___x_665_, v_a_616_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_a_667_, v_binderType_648_, v_arrow_654_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_682_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_682_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_682_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_682_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_v_656_);
lean_inc(v_a_661_);
v___x_673_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_673_, 0, v_binderName_647_);
lean_ctor_set(v___x_673_, 1, v_a_661_);
lean_ctor_set(v___x_673_, 2, v_v_656_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*3, v_binderInfo_650_);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_infos_655_);
v___x_675_ = l_Lean_mkLevelIMax_x27(v_a_661_, v_v_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 2, v___x_675_);
lean_ctor_set(v___x_658_, 1, v___x_674_);
lean_ctor_set(v___x_658_, 0, v_a_669_);
v___x_677_ = v___x_658_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_675_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_677_);
v___x_679_ = v___x_671_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_661_);
lean_del_object(v___x_658_);
lean_dec(v_v_656_);
lean_dec(v_infos_655_);
lean_dec(v_binderName_647_);
v_a_683_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_668_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_668_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_661_);
lean_del_object(v___x_658_);
lean_dec(v_v_656_);
lean_dec(v_infos_655_);
lean_dec_ref(v_arrow_654_);
lean_dec_ref(v_binderType_648_);
lean_dec(v_binderName_647_);
v_a_691_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_666_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_666_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_del_object(v___x_658_);
lean_dec(v_v_656_);
lean_dec(v_infos_655_);
lean_dec_ref(v_arrow_654_);
lean_dec_ref(v_binderType_648_);
lean_dec(v_binderName_647_);
v_a_699_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_660_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_660_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_dec_ref(v_binderType_648_);
lean_dec(v_binderName_647_);
return v___x_652_;
}
}
else
{
v___y_623_ = v_a_616_;
v___y_624_ = v_a_617_;
v___y_625_ = v_a_618_;
v___y_626_ = v_a_619_;
v___y_627_ = v_a_620_;
goto v___jp_622_;
}
}
else
{
v___y_623_ = v_a_616_;
v___y_624_ = v_a_617_;
v___y_625_ = v_a_618_;
v___y_626_ = v_a_619_;
v___y_627_ = v_a_620_;
goto v___jp_622_;
}
v___jp_622_:
{
lean_object* v___x_628_; 
lean_inc_ref(v_e_614_);
v___x_628_ = l_Lean_Meta_Sym_getLevel___redArg(v_e_614_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_634_, 0, v_e_614_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_e_614_);
v_a_639_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_628_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_628_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_614_ = stack[0].m_obj;
lean_object* v_a_615_ = stack[1].m_obj;
lean_object* v_a_616_ = stack[2].m_obj;
lean_object* v_a_617_ = stack[3].m_obj;
lean_object* v_a_618_ = stack[4].m_obj;
lean_object* v_a_619_ = stack[5].m_obj;
lean_object* v_a_620_ = stack[6].m_obj;
lean_object* v_res_708_;
v_res_708_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___boxed(lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(lean_object* v_x_718_, uint8_t v_bi_719_, lean_object* v_t_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___y_730_; lean_object* v___x_733_; uint8_t v_debug_734_; 
v___x_733_ = lean_st_ref_get(v___y_723_);
v_debug_734_ = lean_ctor_get_uint8(v___x_733_, sizeof(void*)*12);
lean_dec(v___x_733_);
if (v_debug_734_ == 0)
{
v___y_730_ = v___y_723_;
goto v___jp_729_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_720_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_736_; 
lean_dec_ref_known(v___x_735_, 1);
v___x_736_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_dec_ref_known(v___x_736_, 1);
v___y_730_ = v___y_723_;
goto v___jp_729_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v_b_721_);
lean_dec_ref(v_t_720_);
lean_dec(v_x_718_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_b_721_);
lean_dec_ref(v_t_720_);
lean_dec(v_x_718_);
v_a_745_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_735_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_735_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
v___jp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = l_Lean_Expr_forallE___override(v_x_718_, v_t_720_, v_b_721_, v_bi_719_);
v___x_732_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_731_, v___y_730_);
return v___x_732_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_718_ = stack[0].m_obj;
uint8_t v_bi_719_ = stack[1].m_num;
lean_object* v_t_720_ = stack[2].m_obj;
lean_object* v_b_721_ = stack[3].m_obj;
lean_object* v___y_722_ = stack[4].m_obj;
lean_object* v___y_723_ = stack[5].m_obj;
lean_object* v___y_724_ = stack[6].m_obj;
lean_object* v___y_725_ = stack[7].m_obj;
lean_object* v___y_726_ = stack[8].m_obj;
lean_object* v___y_727_ = stack[9].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_x_718_, v_bi_719_, v_t_720_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0___boxed(lean_object* v_x_754_, lean_object* v_bi_755_, lean_object* v_t_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_bi_boxed_765_; lean_object* v_res_766_; 
v_bi_boxed_765_ = lean_unbox(v_bi_755_);
v_res_766_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_x_754_, v_bi_boxed_765_, v_t_756_, v_b_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_766_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(lean_object* v_e_767_, lean_object* v_infos_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
if (lean_obj_tag(v_infos_768_) == 1)
{
lean_object* v_head_776_; lean_object* v_tail_777_; lean_object* v_binderName_778_; uint8_t v_binderInfo_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_head_776_ = lean_ctor_get(v_infos_768_, 0);
lean_inc(v_head_776_);
v_tail_777_ = lean_ctor_get(v_infos_768_, 1);
lean_inc(v_tail_777_);
lean_dec_ref_known(v_infos_768_, 2);
v_binderName_778_ = lean_ctor_get(v_head_776_, 0);
lean_inc(v_binderName_778_);
v_binderInfo_779_ = lean_ctor_get_uint8(v_head_776_, sizeof(void*)*3);
lean_dec(v_head_776_);
lean_inc_ref(v_e_767_);
v___x_780_ = l_Lean_Expr_cleanupAnnotations(v_e_767_);
v___x_781_ = l_Lean_Expr_isApp(v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec_ref(v___x_780_);
lean_dec(v_binderName_778_);
lean_dec(v_tail_777_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v_e_767_);
return v___x_782_;
}
else
{
lean_object* v_arg_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_arg_783_ = lean_ctor_get(v___x_780_, 1);
lean_inc_ref(v_arg_783_);
v___x_784_ = l_Lean_Expr_appFnCleanup___redArg(v___x_780_);
v___x_785_ = l_Lean_Expr_isApp(v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_784_);
lean_dec_ref(v_arg_783_);
lean_dec(v_binderName_778_);
lean_dec(v_tail_777_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_e_767_);
return v___x_786_;
}
else
{
lean_object* v_arg_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_arg_787_ = lean_ctor_get(v___x_784_, 1);
lean_inc_ref(v_arg_787_);
v___x_788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_784_);
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_790_ = l_Lean_Expr_isConstOf(v___x_788_, v___x_789_);
lean_dec_ref(v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v_arg_787_);
lean_dec_ref(v_arg_783_);
lean_dec(v_binderName_778_);
lean_dec(v_tail_777_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_e_767_);
return v___x_791_;
}
else
{
lean_object* v___x_792_; 
lean_dec_ref(v_e_767_);
v___x_792_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_arg_783_, v_tail_777_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_binderName_778_, v_binderInfo_779_, v_arg_787_, v_a_793_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
return v___x_794_;
}
else
{
lean_dec_ref(v_arg_787_);
lean_dec(v_binderName_778_);
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_infos_768_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_e_767_);
return v___x_795_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_767_ = stack[0].m_obj;
lean_object* v_infos_768_ = stack[1].m_obj;
lean_object* v_a_769_ = stack[2].m_obj;
lean_object* v_a_770_ = stack[3].m_obj;
lean_object* v_a_771_ = stack[4].m_obj;
lean_object* v_a_772_ = stack[5].m_obj;
lean_object* v_a_773_ = stack[6].m_obj;
lean_object* v_a_774_ = stack[7].m_obj;
lean_object* v_res_796_;
v_res_796_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_767_, v_infos_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall___boxed(lean_object* v_e_797_, lean_object* v_infos_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_797_, v_infos_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_806_;
}
}
uint8_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(lean_object* v_head_807_, lean_object* v_00___808_){
_start:
{
lean_object* v_v_809_; uint8_t v___x_810_; 
v_v_809_ = lean_ctor_get(v_head_807_, 2);
v___x_810_ = l_Lean_Level_isZero(v_v_809_);
return v___x_810_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_807_ = stack[0].m_obj;
lean_object* v_00___808_ = stack[1].m_obj;
uint8_t v_res_811_;
v_res_811_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_807_, v_00___808_);
stack->m_num = v_res_811_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0___boxed(lean_object* v_head_812_, lean_object* v_00___813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_812_, v_00___813_);
lean_dec_ref(v_head_812_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(lean_object* v_f_816_, lean_object* v_a_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___y_826_; lean_object* v___x_829_; uint8_t v_debug_830_; 
v___x_829_ = lean_st_ref_get(v___y_819_);
v_debug_830_ = lean_ctor_get_uint8(v___x_829_, sizeof(void*)*12);
lean_dec(v___x_829_);
if (v_debug_830_ == 0)
{
v___y_826_ = v___y_819_;
goto v___jp_825_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_816_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref_known(v___x_831_, 1);
v___x_832_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref_known(v___x_832_, 1);
v___y_826_ = v___y_819_;
goto v___jp_825_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v_a_817_);
lean_dec_ref(v_f_816_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_a_817_);
lean_dec_ref(v_f_816_);
v_a_841_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_831_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_831_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l_Lean_Expr_app___override(v_f_816_, v_a_817_);
v___x_828_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_827_, v___y_826_);
return v___x_828_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_816_ = stack[0].m_obj;
lean_object* v_a_817_ = stack[1].m_obj;
lean_object* v___y_818_ = stack[2].m_obj;
lean_object* v___y_819_ = stack[3].m_obj;
lean_object* v___y_820_ = stack[4].m_obj;
lean_object* v___y_821_ = stack[5].m_obj;
lean_object* v___y_822_ = stack[6].m_obj;
lean_object* v___y_823_ = stack[7].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_816_, v_a_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(lean_object* v_f_850_, lean_object* v_a_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_850_, v_a_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_859_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(lean_object* v_f_860_, lean_object* v_a_u2081_861_, lean_object* v_a_u2082_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_860_, v_a_u2081_861_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_a_874_, v_a_u2082_862_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_875_;
}
else
{
lean_dec_ref(v_a_u2082_862_);
return v___x_873_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_860_ = stack[0].m_obj;
lean_object* v_a_u2081_861_ = stack[1].m_obj;
lean_object* v_a_u2082_862_ = stack[2].m_obj;
lean_object* v___y_863_ = stack[3].m_obj;
lean_object* v___y_864_ = stack[4].m_obj;
lean_object* v___y_865_ = stack[5].m_obj;
lean_object* v___y_866_ = stack[6].m_obj;
lean_object* v___y_867_ = stack[7].m_obj;
lean_object* v___y_868_ = stack[8].m_obj;
lean_object* v___y_869_ = stack[9].m_obj;
lean_object* v___y_870_ = stack[10].m_obj;
lean_object* v___y_871_ = stack[11].m_obj;
lean_object* v_res_876_;
v_res_876_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v_f_860_, v_a_u2081_861_, v_a_u2082_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(lean_object* v_f_877_, lean_object* v_a_u2081_878_, lean_object* v_a_u2082_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v_f_877_, v_a_u2081_878_, v_a_u2082_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
return v_res_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_box(0);
v___x_916_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11));
v___x_917_ = l_Lean_mkConst(v___x_916_, v___x_915_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14));
v___x_924_ = l_Lean_mkConst(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17));
v___x_931_ = l_Lean_mkConst(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_box(0);
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20));
v___x_938_ = l_Lean_mkConst(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_box(0);
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23));
v___x_945_ = l_Lean_mkConst(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26));
v___x_952_ = l_Lean_mkConst(v___x_951_, v___x_950_);
return v___x_952_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(lean_object* v_e_953_, lean_object* v_infos_954_, lean_object* v_simpBody_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
uint8_t v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; uint8_t v___y_976_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; 
if (lean_obj_tag(v_infos_954_) == 0)
{
lean_object* v___x_1008_; 
lean_inc(v_a_964_);
lean_inc_ref(v_a_963_);
lean_inc(v_a_962_);
lean_inc_ref(v_a_961_);
lean_inc(v_a_960_);
lean_inc_ref(v_a_959_);
lean_inc(v_a_958_);
lean_inc_ref(v_a_957_);
lean_inc(v_a_956_);
v___x_1008_ = lean_apply_11(v_simpBody_955_, v_e_953_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, lean_box(0));
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_a_1009_);
lean_ctor_set(v___x_1013_, 1, v_infos_954_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1008_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1008_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_head_1026_; lean_object* v_tail_1027_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; uint8_t v___y_1033_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_head_1026_ = lean_ctor_get(v_infos_954_, 0);
v_tail_1027_ = lean_ctor_get(v_infos_954_, 1);
lean_inc_ref(v_e_953_);
v___x_1038_ = l_Lean_Expr_cleanupAnnotations(v_e_953_);
v___x_1039_ = l_Lean_Expr_isApp(v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec_ref(v___x_1038_);
v___y_981_ = v_a_956_;
v___y_982_ = v_a_957_;
v___y_983_ = v_a_958_;
v___y_984_ = v_a_959_;
v___y_985_ = v_a_960_;
v___y_986_ = v_a_961_;
v___y_987_ = v_a_962_;
v___y_988_ = v_a_963_;
v___y_989_ = v_a_964_;
goto v___jp_980_;
}
else
{
lean_object* v_arg_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_arg_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc_ref(v_arg_1040_);
v___x_1041_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1038_);
v___x_1042_ = l_Lean_Expr_isApp(v___x_1041_);
if (v___x_1042_ == 0)
{
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_arg_1040_);
v___y_981_ = v_a_956_;
v___y_982_ = v_a_957_;
v___y_983_ = v_a_958_;
v___y_984_ = v_a_959_;
v___y_985_ = v_a_960_;
v___y_986_ = v_a_961_;
v___y_987_ = v_a_962_;
v___y_988_ = v_a_963_;
v___y_989_ = v_a_964_;
goto v___jp_980_;
}
else
{
lean_object* v_arg_1043_; lean_object* v___x_1044_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; uint8_t v___y_1050_; lean_object* v___y_1076_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v_proof_1134_; uint8_t v___y_1135_; uint8_t v___y_1136_; lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; uint8_t v___y_1171_; uint8_t v___y_1172_; lean_object* v___y_1188_; uint8_t v___y_1189_; uint8_t v___y_1190_; 
v_arg_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc_ref(v_arg_1043_);
v___x_1044_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1041_);
v___x_1162_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_1163_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
v___y_981_ = v_a_956_;
v___y_982_ = v_a_957_;
v___y_983_ = v_a_958_;
v___y_984_ = v_a_959_;
v___y_985_ = v_a_960_;
v___y_986_ = v_a_961_;
v___y_987_ = v_a_962_;
v___y_988_ = v_a_963_;
v___y_989_ = v_a_964_;
goto v___jp_980_;
}
else
{
lean_object* v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; uint8_t v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1260_; lean_object* v___x_1293_; 
lean_dec_ref(v_e_953_);
lean_inc(v_a_964_);
lean_inc_ref(v_a_963_);
lean_inc(v_a_962_);
lean_inc_ref(v_a_961_);
lean_inc(v_a_960_);
lean_inc_ref(v_a_959_);
lean_inc(v_a_958_);
lean_inc_ref(v_a_957_);
lean_inc(v_a_956_);
lean_inc_ref(v_arg_1043_);
v___x_1293_ = lean_sym_simp(v_arg_1043_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1043_, v_a_1294_);
v___x_1296_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v___x_1295_, v_a_959_);
lean_dec_ref(v___x_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; uint8_t v___y_1299_; uint8_t v___x_1362_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1362_ = lean_unbox(v_a_1297_);
if (v___x_1362_ == 0)
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_unbox(v_a_1297_);
lean_dec(v_a_1297_);
v___y_1299_ = v___x_1363_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
lean_dec(v_a_1297_);
v___x_1364_ = lean_box(0);
v___x_1365_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1026_, v___x_1364_);
if (v___x_1365_ == 0)
{
v___y_1299_ = v___x_1365_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_simpBody_955_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_infos_954_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1430_ = lean_ctor_get(v_infos_954_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_infos_954_, 0);
lean_dec(v_unused_1431_);
v___x_1367_ = v_infos_954_;
v_isShared_1368_ = v_isSharedCheck_1429_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v_infos_954_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1429_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
if (lean_obj_tag(v_a_1294_) == 0)
{
uint8_t v_contextDependent_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v_arg_1043_);
v_contextDependent_1369_ = lean_ctor_get_uint8(v_a_1294_, 1);
lean_dec_ref_known(v_a_1294_, 0);
v___x_1370_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_959_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1386_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1386_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1386_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24);
v___x_1377_ = l_Lean_Expr_app___override(v___x_1376_, v_arg_1040_);
v___x_1378_ = 0;
v___x_1379_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1379_, 0, v_a_1371_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*2, v___x_1378_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*2 + 1, v_contextDependent_1369_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
lean_ctor_set(v___x_1367_, 1, v___x_1375_);
lean_ctor_set(v___x_1367_, 0, v___x_1379_);
v___x_1381_ = v___x_1367_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1375_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1383_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1381_);
v___x_1383_ = v___x_1373_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
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
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_del_object(v___x_1367_);
lean_dec_ref(v_arg_1040_);
v_a_1387_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1370_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1370_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_proof_1395_; uint8_t v_contextDependent_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1427_; 
v_proof_1395_ = lean_ctor_get(v_a_1294_, 1);
v_contextDependent_1396_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*2 + 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_a_1294_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_a_1294_, 0);
lean_dec(v_unused_1428_);
v___x_1398_ = v_a_1294_;
v_isShared_1399_ = v_isSharedCheck_1427_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_proof_1395_);
lean_dec(v_a_1294_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1427_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_959_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1418_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1418_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1418_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1410_; 
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27);
v___x_1407_ = l_Lean_mkApp3(v___x_1406_, v_arg_1043_, v_arg_1040_, v_proof_1395_);
v___x_1408_ = 0;
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1407_);
lean_ctor_set(v___x_1398_, 0, v_a_1401_);
v___x_1410_ = v___x_1398_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1401_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1417_, sizeof(void*)*2 + 1, v_contextDependent_1396_);
v___x_1410_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*2, v___x_1408_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
lean_ctor_set(v___x_1367_, 1, v___x_1405_);
lean_ctor_set(v___x_1367_, 0, v___x_1410_);
v___x_1412_ = v___x_1367_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1405_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1412_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1398_);
lean_dec_ref(v_proof_1395_);
lean_del_object(v___x_1367_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
v_a_1419_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1400_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1400_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
}
}
v___jp_1298_:
{
lean_object* v___x_1300_; 
lean_inc(v_tail_1027_);
lean_inc_ref(v_arg_1040_);
v___x_1300_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arg_1040_, v_tail_1027_, v_simpBody_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_fst_1302_ = lean_ctor_get(v_a_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v_a_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec(v_a_1301_);
v___x_1304_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1040_, v_fst_1302_);
v___x_1305_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___x_1304_, v_a_959_);
lean_dec_ref(v___x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; uint8_t v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = lean_unbox(v_a_1306_);
if (v___x_1307_ == 0)
{
if (lean_obj_tag(v_a_1294_) == 0)
{
if (lean_obj_tag(v_fst_1302_) == 0)
{
uint8_t v_contextDependent_1308_; 
lean_dec_ref(v___x_1044_);
v_contextDependent_1308_ = lean_ctor_get_uint8(v_a_1294_, 1);
lean_dec_ref_known(v_a_1294_, 0);
if (v_contextDependent_1308_ == 0)
{
uint8_t v_contextDependent_1309_; uint8_t v___x_1310_; 
v_contextDependent_1309_ = lean_ctor_get_uint8(v_fst_1302_, 1);
lean_dec_ref_known(v_fst_1302_, 0);
v___x_1310_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_1258_ = v___x_1310_;
v___y_1259_ = v_snd_1303_;
v___y_1260_ = v_contextDependent_1309_;
goto v___jp_1257_;
}
else
{
uint8_t v___x_1311_; 
lean_dec_ref_known(v_fst_1302_, 0);
v___x_1311_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_1258_ = v___x_1311_;
v___y_1259_ = v_snd_1303_;
v___y_1260_ = v___x_1163_;
goto v___jp_1257_;
}
}
else
{
uint8_t v_contextDependent_1312_; 
lean_inc(v_head_1026_);
lean_dec_ref_known(v_infos_954_, 2);
v_contextDependent_1312_ = lean_ctor_get_uint8(v_a_1294_, 1);
lean_dec_ref_known(v_a_1294_, 0);
if (v_contextDependent_1312_ == 0)
{
lean_object* v_e_x27_1313_; lean_object* v_proof_1314_; uint8_t v_contextDependent_1315_; uint8_t v___x_1316_; 
v_e_x27_1313_ = lean_ctor_get(v_fst_1302_, 0);
lean_inc_ref(v_e_x27_1313_);
v_proof_1314_ = lean_ctor_get(v_fst_1302_, 1);
lean_inc_ref(v_proof_1314_);
v_contextDependent_1315_ = lean_ctor_get_uint8(v_fst_1302_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1302_, 2);
v___x_1316_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_1227_ = v_e_x27_1313_;
v___y_1228_ = v_proof_1314_;
v___y_1229_ = v___x_1316_;
v___y_1230_ = v_snd_1303_;
v___y_1231_ = v_contextDependent_1315_;
goto v___jp_1226_;
}
else
{
lean_object* v_e_x27_1317_; lean_object* v_proof_1318_; uint8_t v___x_1319_; 
v_e_x27_1317_ = lean_ctor_get(v_fst_1302_, 0);
lean_inc_ref(v_e_x27_1317_);
v_proof_1318_ = lean_ctor_get(v_fst_1302_, 1);
lean_inc_ref(v_proof_1318_);
lean_dec_ref_known(v_fst_1302_, 2);
v___x_1319_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_1227_ = v_e_x27_1317_;
v___y_1228_ = v_proof_1318_;
v___y_1229_ = v___x_1319_;
v___y_1230_ = v_snd_1303_;
v___y_1231_ = v___x_1163_;
goto v___jp_1226_;
}
}
}
else
{
lean_inc(v_head_1026_);
lean_dec_ref_known(v_infos_954_, 2);
if (lean_obj_tag(v_fst_1302_) == 0)
{
uint8_t v_contextDependent_1320_; 
v_contextDependent_1320_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*2 + 1);
if (v_contextDependent_1320_ == 0)
{
lean_object* v_e_x27_1321_; lean_object* v_proof_1322_; uint8_t v_contextDependent_1323_; uint8_t v___x_1324_; 
v_e_x27_1321_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_e_x27_1321_);
v_proof_1322_ = lean_ctor_get(v_a_1294_, 1);
lean_inc_ref(v_proof_1322_);
lean_dec_ref_known(v_a_1294_, 2);
v_contextDependent_1323_ = lean_ctor_get_uint8(v_fst_1302_, 1);
lean_dec_ref_known(v_fst_1302_, 0);
v___x_1324_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_1196_ = v_e_x27_1321_;
v___y_1197_ = v___x_1324_;
v___y_1198_ = v_snd_1303_;
v___y_1199_ = v_proof_1322_;
v___y_1200_ = v_contextDependent_1323_;
goto v___jp_1195_;
}
else
{
lean_object* v_e_x27_1325_; lean_object* v_proof_1326_; uint8_t v___x_1327_; 
lean_dec_ref_known(v_fst_1302_, 0);
v_e_x27_1325_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_e_x27_1325_);
v_proof_1326_ = lean_ctor_get(v_a_1294_, 1);
lean_inc_ref(v_proof_1326_);
lean_dec_ref_known(v_a_1294_, 2);
v___x_1327_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_1196_ = v_e_x27_1325_;
v___y_1197_ = v___x_1327_;
v___y_1198_ = v_snd_1303_;
v___y_1199_ = v_proof_1326_;
v___y_1200_ = v___x_1163_;
goto v___jp_1195_;
}
}
else
{
lean_object* v_e_x27_1328_; lean_object* v_proof_1329_; uint8_t v_contextDependent_1330_; lean_object* v_e_x27_1331_; lean_object* v_proof_1332_; uint8_t v_contextDependent_1333_; lean_object* v___x_1334_; 
v_e_x27_1328_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_e_x27_1328_);
v_proof_1329_ = lean_ctor_get(v_a_1294_, 1);
lean_inc_ref(v_proof_1329_);
v_contextDependent_1330_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1294_, 2);
v_e_x27_1331_ = lean_ctor_get(v_fst_1302_, 0);
lean_inc_ref(v_e_x27_1331_);
v_proof_1332_ = lean_ctor_get(v_fst_1302_, 1);
lean_inc_ref(v_proof_1332_);
v_contextDependent_1333_ = lean_ctor_get_uint8(v_fst_1302_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1302_, 2);
v___x_1334_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1328_, v_a_959_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; uint8_t v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = lean_unbox(v_a_1335_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; 
lean_dec(v_a_1306_);
v___x_1337_ = lean_unbox(v_a_1335_);
lean_dec(v_a_1335_);
v___y_1165_ = v_e_x27_1328_;
v___y_1166_ = v_proof_1332_;
v___y_1167_ = v_e_x27_1331_;
v___y_1168_ = v_snd_1303_;
v___y_1169_ = v_contextDependent_1333_;
v___y_1170_ = v_proof_1329_;
v___y_1171_ = v_contextDependent_1330_;
v___y_1172_ = v___x_1337_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
lean_dec(v_a_1335_);
v___x_1338_ = lean_box(0);
v___x_1339_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1026_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v_a_1306_);
v___y_1165_ = v_e_x27_1328_;
v___y_1166_ = v_proof_1332_;
v___y_1167_ = v_e_x27_1331_;
v___y_1168_ = v_snd_1303_;
v___y_1169_ = v_contextDependent_1333_;
v___y_1170_ = v_proof_1329_;
v___y_1171_ = v_contextDependent_1330_;
v___y_1172_ = v___x_1339_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v_e_x27_1328_);
lean_dec_ref(v___x_1044_);
lean_dec(v_head_1026_);
v___x_1340_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21);
lean_inc_ref(v_e_x27_1331_);
v___x_1341_ = l_Lean_mkApp5(v___x_1340_, v_arg_1043_, v_arg_1040_, v_e_x27_1331_, v_proof_1329_, v_proof_1332_);
if (v_contextDependent_1330_ == 0)
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_967_ = v___x_1342_;
v___y_968_ = v_e_x27_1331_;
v___y_969_ = v_snd_1303_;
v___y_970_ = v___x_1341_;
v___y_971_ = v_contextDependent_1333_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___y_967_ = v___x_1343_;
v___y_968_ = v_e_x27_1331_;
v___y_969_ = v_snd_1303_;
v___y_970_ = v___x_1341_;
v___y_971_ = v___x_1163_;
goto v___jp_966_;
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_proof_1332_);
lean_dec_ref(v_e_x27_1331_);
lean_dec_ref(v_proof_1329_);
lean_dec_ref(v_e_x27_1328_);
lean_dec(v_a_1306_);
lean_dec(v_snd_1303_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1344_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1334_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1334_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
else
{
lean_inc(v_head_1026_);
lean_dec(v_a_1306_);
lean_dec(v_snd_1303_);
lean_dec_ref(v___x_1044_);
lean_dec_ref_known(v_infos_954_, 2);
if (lean_obj_tag(v_a_1294_) == 0)
{
uint8_t v_contextDependent_1352_; 
v_contextDependent_1352_ = lean_ctor_get_uint8(v_a_1294_, 1);
lean_dec_ref_known(v_a_1294_, 0);
v___y_1188_ = v_fst_1302_;
v___y_1189_ = v___y_1299_;
v___y_1190_ = v_contextDependent_1352_;
goto v___jp_1187_;
}
else
{
uint8_t v_contextDependent_1353_; 
v_contextDependent_1353_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1294_, 2);
v___y_1188_ = v_fst_1302_;
v___y_1189_ = v___y_1299_;
v___y_1190_ = v_contextDependent_1353_;
goto v___jp_1187_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
lean_dec(v_a_1294_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec_ref_known(v_infos_954_, 2);
v_a_1354_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1305_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1305_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_dec(v_a_1294_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec_ref_known(v_infos_954_, 2);
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_a_1294_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec_ref_known(v_infos_954_, 2);
lean_dec_ref(v_simpBody_955_);
v_a_1432_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1296_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1296_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec_ref_known(v_infos_954_, 2);
lean_dec_ref(v_simpBody_955_);
v_a_1440_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1293_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1293_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
v___jp_1195_:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___y_1196_, v_a_959_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1217_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1217_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1217_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_unbox(v_a_1202_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; 
lean_del_object(v___x_1204_);
v___x_1207_ = lean_unbox(v_a_1202_);
lean_dec(v_a_1202_);
v___y_1046_ = v___y_1196_;
v___y_1047_ = v___y_1198_;
v___y_1048_ = v___y_1199_;
v___y_1049_ = v___y_1200_;
v___y_1050_ = v___x_1207_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
lean_dec(v_a_1202_);
v___x_1208_ = lean_box(0);
v___x_1209_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1026_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_del_object(v___x_1204_);
v___y_1046_ = v___y_1196_;
v___y_1047_ = v___y_1198_;
v___y_1048_ = v___y_1199_;
v___y_1049_ = v___y_1200_;
v___y_1050_ = v___x_1209_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___x_1044_);
lean_dec(v_head_1026_);
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12);
lean_inc_ref(v_arg_1040_);
v___x_1211_ = l_Lean_mkApp3(v___x_1210_, v_arg_1043_, v_arg_1040_, v___y_1199_);
v___x_1212_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1212_, 0, v_arg_1040_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*2, v___y_1197_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*2 + 1, v___y_1200_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___y_1198_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1213_);
v___x_1215_ = v___x_1204_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
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
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1218_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1201_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1201_);
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
v___jp_1226_:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1043_, v_a_959_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1248_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1248_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1248_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_unbox(v_a_1233_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; 
lean_del_object(v___x_1235_);
v___x_1238_ = lean_unbox(v_a_1233_);
lean_dec(v_a_1233_);
v___y_1076_ = v___y_1228_;
v___y_1077_ = v___y_1227_;
v___y_1078_ = v___y_1231_;
v___y_1079_ = v___y_1230_;
v___y_1080_ = v___x_1238_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
lean_dec(v_a_1233_);
v___x_1239_ = lean_box(0);
v___x_1240_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1026_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_del_object(v___x_1235_);
v___y_1076_ = v___y_1228_;
v___y_1077_ = v___y_1227_;
v___y_1078_ = v___y_1231_;
v___y_1079_ = v___y_1230_;
v___y_1080_ = v___x_1240_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec(v_head_1026_);
v___x_1241_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15);
lean_inc_ref(v___y_1227_);
v___x_1242_ = l_Lean_mkApp3(v___x_1241_, v_arg_1040_, v___y_1227_, v___y_1228_);
v___x_1243_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1243_, 0, v___y_1227_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*2, v___y_1229_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*2 + 1, v___y_1231_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___y_1230_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1244_);
v___x_1246_ = v___x_1235_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
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
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1249_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1232_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1232_);
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
v___jp_1257_:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1043_, v_a_959_);
lean_dec_ref(v_arg_1043_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1284_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1284_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1284_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
if (v___x_1266_ == 0)
{
lean_del_object(v___x_1264_);
lean_dec(v___y_1259_);
lean_dec_ref(v_arg_1040_);
v___y_976_ = v___y_1260_;
goto v___jp_975_;
}
else
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1026_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_del_object(v___x_1264_);
lean_dec(v___y_1259_);
lean_dec_ref(v_arg_1040_);
v___y_976_ = v___y_1260_;
goto v___jp_975_;
}
else
{
lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1281_; 
v_isSharedCheck_1281_ = !lean_is_exclusive(v_infos_954_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; lean_object* v_unused_1283_; 
v_unused_1282_ = lean_ctor_get(v_infos_954_, 1);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_infos_954_, 0);
lean_dec(v_unused_1283_);
v___x_1270_ = v_infos_954_;
v_isShared_1271_ = v_isSharedCheck_1281_;
goto v_resetjp_1269_;
}
else
{
lean_dec(v_infos_954_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1281_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1272_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18);
lean_inc_ref(v_arg_1040_);
v___x_1273_ = l_Lean_Expr_app___override(v___x_1272_, v_arg_1040_);
v___x_1274_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1274_, 0, v_arg_1040_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*2, v___y_1258_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*2 + 1, v___y_1260_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
lean_ctor_set(v___x_1270_, 1, v___y_1259_);
lean_ctor_set(v___x_1270_, 0, v___x_1274_);
v___x_1276_ = v___x_1270_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___y_1259_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1276_);
v___x_1278_ = v___x_1264_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
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
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v___y_1259_);
lean_dec_ref(v_arg_1040_);
lean_dec_ref_known(v_infos_954_, 2);
v_a_1285_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1261_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1261_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
v___jp_1045_:
{
lean_object* v___x_1051_; 
lean_inc_ref(v_arg_1040_);
lean_inc_ref(v___y_1046_);
lean_inc_ref(v___x_1044_);
v___x_1051_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1044_, v___y_1046_, v_arg_1040_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1066_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1056_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1));
v___x_1057_ = l_Lean_Expr_constLevels_x21(v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1058_ = l_Lean_mkConst(v___x_1056_, v___x_1057_);
v___x_1059_ = l_Lean_mkApp4(v___x_1058_, v_arg_1043_, v___y_1046_, v_arg_1040_, v___y_1048_);
v___x_1060_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1060_, 0, v_a_1052_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*2, v___y_1050_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*2 + 1, v___y_1049_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_head_1026_);
lean_ctor_set(v___x_1061_, 1, v___y_1047_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1062_);
v___x_1064_ = v___x_1054_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1067_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1051_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1051_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
v___jp_1075_:
{
lean_object* v___x_1081_; 
lean_inc_ref(v___y_1077_);
lean_inc_ref(v_arg_1043_);
lean_inc_ref(v___x_1044_);
v___x_1081_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1044_, v_arg_1043_, v___y_1077_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1096_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1096_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1096_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3));
v___x_1087_ = l_Lean_Expr_constLevels_x21(v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1088_ = l_Lean_mkConst(v___x_1086_, v___x_1087_);
v___x_1089_ = l_Lean_mkApp4(v___x_1088_, v_arg_1043_, v_arg_1040_, v___y_1077_, v___y_1076_);
v___x_1090_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1090_, 0, v_a_1082_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*2, v___y_1080_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*2 + 1, v___y_1078_);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_head_1026_);
lean_ctor_set(v___x_1091_, 1, v___y_1079_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1092_);
v___x_1094_ = v___x_1084_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1097_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1081_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1081_);
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
v___jp_1105_:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_959_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1124_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_u_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_u_1113_ = lean_ctor_get(v_head_1026_, 1);
lean_inc(v_u_1113_);
lean_dec(v_head_1026_);
v___x_1114_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5));
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_u_1113_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_mkConst(v___x_1114_, v___x_1116_);
v___x_1118_ = l_Lean_Expr_app___override(v___x_1117_, v_arg_1043_);
v___x_1119_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1119_, 0, v_a_1109_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*2, v___y_1106_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*2 + 1, v___y_1107_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1115_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_arg_1043_);
lean_dec(v_head_1026_);
v_a_1125_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1108_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1108_);
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
v___jp_1133_:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_959_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1153_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1153_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1153_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_u_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v_u_1142_ = lean_ctor_get(v_head_1026_, 1);
lean_inc(v_u_1142_);
lean_dec(v_head_1026_);
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7));
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_u_1142_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_mkConst(v___x_1143_, v___x_1145_);
v___x_1147_ = l_Lean_mkApp3(v___x_1146_, v_arg_1043_, v_arg_1040_, v_proof_1134_);
v___x_1148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1148_, 0, v_a_1138_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*2, v___y_1135_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*2 + 1, v___y_1136_);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v___x_1144_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1149_);
v___x_1151_ = v___x_1140_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_proof_1134_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1154_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1137_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1137_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
v___jp_1164_:
{
lean_object* v___x_1173_; 
lean_inc_ref(v___y_1167_);
lean_inc_ref(v___y_1165_);
lean_inc_ref(v___x_1044_);
v___x_1173_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1044_, v___y_1165_, v___y_1167_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9));
v___x_1176_ = l_Lean_Expr_constLevels_x21(v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1177_ = l_Lean_mkConst(v___x_1175_, v___x_1176_);
v___x_1178_ = l_Lean_mkApp6(v___x_1177_, v_arg_1043_, v___y_1165_, v_arg_1040_, v___y_1167_, v___y_1170_, v___y_1166_);
if (v___y_1171_ == 0)
{
v___y_1029_ = v_a_1174_;
v___y_1030_ = v___y_1168_;
v___y_1031_ = v___x_1178_;
v___y_1032_ = v___y_1172_;
v___y_1033_ = v___y_1169_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v_a_1174_;
v___y_1030_ = v___y_1168_;
v___y_1031_ = v___x_1178_;
v___y_1032_ = v___y_1172_;
v___y_1033_ = v___x_1163_;
goto v___jp_1028_;
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1040_);
lean_dec(v_head_1026_);
v_a_1179_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1173_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1173_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
v___jp_1187_:
{
if (v___y_1190_ == 0)
{
if (lean_obj_tag(v___y_1188_) == 0)
{
uint8_t v_contextDependent_1191_; 
lean_dec_ref(v_arg_1040_);
v_contextDependent_1191_ = lean_ctor_get_uint8(v___y_1188_, 1);
lean_dec_ref_known(v___y_1188_, 0);
v___y_1106_ = v___y_1189_;
v___y_1107_ = v_contextDependent_1191_;
goto v___jp_1105_;
}
else
{
lean_object* v_proof_1192_; uint8_t v_contextDependent_1193_; 
v_proof_1192_ = lean_ctor_get(v___y_1188_, 1);
lean_inc_ref(v_proof_1192_);
v_contextDependent_1193_ = lean_ctor_get_uint8(v___y_1188_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_1188_, 2);
v_proof_1134_ = v_proof_1192_;
v___y_1135_ = v___y_1189_;
v___y_1136_ = v_contextDependent_1193_;
goto v___jp_1133_;
}
}
else
{
if (lean_obj_tag(v___y_1188_) == 0)
{
lean_dec_ref_known(v___y_1188_, 0);
lean_dec_ref(v_arg_1040_);
v___y_1106_ = v___y_1189_;
v___y_1107_ = v___x_1163_;
goto v___jp_1105_;
}
else
{
lean_object* v_proof_1194_; 
v_proof_1194_ = lean_ctor_get(v___y_1188_, 1);
lean_inc_ref(v_proof_1194_);
lean_dec_ref_known(v___y_1188_, 2);
v_proof_1134_ = v_proof_1194_;
v___y_1135_ = v___y_1189_;
v___y_1136_ = v___x_1163_;
goto v___jp_1133_;
}
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1034_, 0, v___y_1029_);
lean_ctor_set(v___x_1034_, 1, v___y_1031_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*2, v___y_1032_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*2 + 1, v___y_1033_);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_head_1026_);
lean_ctor_set(v___x_1035_, 1, v___y_1030_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
v___jp_966_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_972_, 0, v___y_968_);
lean_ctor_set(v___x_972_, 1, v___y_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*2, v___y_967_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*2 + 1, v___y_971_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___y_969_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_976_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_infos_954_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
v___jp_980_:
{
lean_object* v___x_990_; 
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
v___x_990_ = lean_apply_11(v_simpBody_955_, v_e_953_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, lean_box(0));
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_a_991_);
lean_ctor_set(v___x_995_, 1, v_infos_954_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_infos_954_);
v_a_1000_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_990_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_990_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_953_ = stack[0].m_obj;
lean_object* v_infos_954_ = stack[1].m_obj;
lean_object* v_simpBody_955_ = stack[2].m_obj;
lean_object* v_a_956_ = stack[3].m_obj;
lean_object* v_a_957_ = stack[4].m_obj;
lean_object* v_a_958_ = stack[5].m_obj;
lean_object* v_a_959_ = stack[6].m_obj;
lean_object* v_a_960_ = stack[7].m_obj;
lean_object* v_a_961_ = stack[8].m_obj;
lean_object* v_a_962_ = stack[9].m_obj;
lean_object* v_a_963_ = stack[10].m_obj;
lean_object* v_a_964_ = stack[11].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_e_953_, v_infos_954_, v_simpBody_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___boxed(lean_object* v_e_1449_, lean_object* v_infos_1450_, lean_object* v_simpBody_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_e_1449_, v_infos_1450_, v_simpBody_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
return v_res_1462_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(lean_object* v_f_1463_, lean_object* v_a_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_1463_, v_a_1464_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1463_ = stack[0].m_obj;
lean_object* v_a_1464_ = stack[1].m_obj;
lean_object* v___y_1465_ = stack[2].m_obj;
lean_object* v___y_1466_ = stack[3].m_obj;
lean_object* v___y_1467_ = stack[4].m_obj;
lean_object* v___y_1468_ = stack[5].m_obj;
lean_object* v___y_1469_ = stack[6].m_obj;
lean_object* v___y_1470_ = stack[7].m_obj;
lean_object* v___y_1471_ = stack[8].m_obj;
lean_object* v___y_1472_ = stack[9].m_obj;
lean_object* v___y_1473_ = stack[10].m_obj;
lean_object* v_res_1476_;
v_res_1476_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(v_f_1463_, v_a_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
stack->m_obj
 = v_res_1476_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___boxed(lean_object* v_f_1477_, lean_object* v_a_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(v_f_1477_, v_a_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
return v_res_1489_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object* v_simpBody_1497_, lean_object* v_e_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Lean_Expr_isArrow(v_e_1498_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_e_1498_);
lean_dec_ref(v_simpBody_1497_);
v___x_1510_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1510_, 0, v___x_1509_);
lean_ctor_set_uint8(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
lean_inc_ref(v_e_1498_);
v___x_1512_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_e_1498_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v_arrow_1514_; lean_object* v_infos_1515_; lean_object* v_v_1516_; lean_object* v___x_1517_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v_arrow_1514_ = lean_ctor_get(v_a_1513_, 0);
lean_inc_ref_n(v_arrow_1514_, 2);
v_infos_1515_ = lean_ctor_get(v_a_1513_, 1);
lean_inc(v_infos_1515_);
v_v_1516_ = lean_ctor_get(v_a_1513_, 2);
lean_inc(v_v_1516_);
lean_dec(v_a_1513_);
v___x_1517_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arrow_1514_, v_infos_1515_, v_simpBody_1497_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1575_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1575_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1575_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_fst_1522_; 
v_fst_1522_ = lean_ctor_get(v_a_1518_, 0);
lean_inc(v_fst_1522_);
if (lean_obj_tag(v_fst_1522_) == 0)
{
uint8_t v_contextDependent_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_dec(v_a_1518_);
lean_dec(v_v_1516_);
lean_dec_ref(v_arrow_1514_);
lean_dec_ref(v_e_1498_);
v_contextDependent_1523_ = lean_ctor_get_uint8(v_fst_1522_, 1);
lean_dec_ref_known(v_fst_1522_, 0);
v___x_1524_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1509_, v_contextDependent_1523_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1526_ = v___x_1520_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
else
{
lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1573_; 
lean_del_object(v___x_1520_);
v_snd_1528_ = lean_ctor_get(v_a_1518_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_a_1518_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_a_1518_, 0);
lean_dec(v_unused_1574_);
v___x_1530_ = v_a_1518_;
v_isShared_1531_ = v_isSharedCheck_1573_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_dec(v_a_1518_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1573_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_e_x27_1532_; lean_object* v_proof_1533_; uint8_t v_contextDependent_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1572_; 
v_e_x27_1532_ = lean_ctor_get(v_fst_1522_, 0);
v_proof_1533_ = lean_ctor_get(v_fst_1522_, 1);
v_contextDependent_1534_ = lean_ctor_get_uint8(v_fst_1522_, sizeof(void*)*2 + 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_fst_1522_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1536_ = v_fst_1522_;
v_isShared_1537_ = v_isSharedCheck_1572_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_proof_1533_);
lean_inc(v_e_x27_1532_);
lean_dec(v_fst_1522_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1572_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; 
lean_inc_ref(v_e_x27_1532_);
v___x_1538_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_e_x27_1532_, v_snd_1528_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1563_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1563_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1563_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_inc(v_v_1516_);
v___x_1543_ = l_Lean_mkSort(v_v_1516_);
v___x_1544_ = l_Lean_Level_succ___override(v_v_1516_);
v___x_1545_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1));
v___x_1546_ = lean_box(0);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 1);
lean_ctor_set(v___x_1530_, 1, v___x_1546_);
lean_ctor_set(v___x_1530_, 0, v___x_1544_);
v___x_1548_ = v___x_1530_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_inc_ref(v___x_1548_);
v___x_1549_ = l_Lean_mkConst(v___x_1545_, v___x_1548_);
v___x_1550_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2));
v___x_1551_ = l_Lean_mkConst(v___x_1550_, v___x_1548_);
lean_inc_ref(v_arrow_1514_);
lean_inc_ref_n(v___x_1543_, 3);
lean_inc_ref(v___x_1551_);
v___x_1552_ = l_Lean_mkAppB(v___x_1551_, v___x_1543_, v_arrow_1514_);
lean_inc_ref(v_e_x27_1532_);
lean_inc_ref(v_e_1498_);
lean_inc_ref(v___x_1549_);
v___x_1553_ = l_Lean_mkApp6(v___x_1549_, v___x_1543_, v_e_1498_, v_arrow_1514_, v_e_x27_1532_, v___x_1552_, v_proof_1533_);
lean_inc_n(v_a_1539_, 2);
v___x_1554_ = l_Lean_mkAppB(v___x_1551_, v___x_1543_, v_a_1539_);
v___x_1555_ = l_Lean_mkApp6(v___x_1549_, v___x_1543_, v_e_1498_, v_e_x27_1532_, v_a_1539_, v___x_1553_, v___x_1554_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v___x_1555_);
lean_ctor_set(v___x_1536_, 0, v_a_1539_);
v___x_1557_ = v___x_1536_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1539_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*2 + 1, v_contextDependent_1534_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*2, v___x_1509_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1557_);
v___x_1559_ = v___x_1541_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
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
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1536_);
lean_dec_ref(v_proof_1533_);
lean_dec_ref(v_e_x27_1532_);
lean_del_object(v___x_1530_);
lean_dec(v_v_1516_);
lean_dec_ref(v_arrow_1514_);
lean_dec_ref(v_e_1498_);
v_a_1564_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1538_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1538_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
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
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_v_1516_);
lean_dec_ref(v_arrow_1514_);
lean_dec_ref(v_e_1498_);
v_a_1576_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1517_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1517_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_e_1498_);
lean_dec_ref(v_simpBody_1497_);
v_a_1584_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1512_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1512_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpArrowTelescope_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_1497_ = stack[0].m_obj;
lean_object* v_e_1498_ = stack[1].m_obj;
lean_object* v_a_1499_ = stack[2].m_obj;
lean_object* v_a_1500_ = stack[3].m_obj;
lean_object* v_a_1501_ = stack[4].m_obj;
lean_object* v_a_1502_ = stack[5].m_obj;
lean_object* v_a_1503_ = stack[6].m_obj;
lean_object* v_a_1504_ = stack[7].m_obj;
lean_object* v_a_1505_ = stack[8].m_obj;
lean_object* v_a_1506_ = stack[9].m_obj;
lean_object* v_a_1507_ = stack[10].m_obj;
lean_object* v_res_1592_;
v_res_1592_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v_simpBody_1497_, v_e_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
stack->m_obj
 = v_res_1592_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed(lean_object* v_simpBody_1593_, lean_object* v_e_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v_simpBody_1593_, v_e_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
return v_res_1605_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(lean_object* v_x_1606_, uint8_t v_bi_1607_, lean_object* v_t_1608_, lean_object* v_b_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___y_1618_; lean_object* v___x_1621_; uint8_t v_debug_1622_; 
v___x_1621_ = lean_st_ref_get(v___y_1611_);
v_debug_1622_ = lean_ctor_get_uint8(v___x_1621_, sizeof(void*)*12);
lean_dec(v___x_1621_);
if (v_debug_1622_ == 0)
{
v___y_1618_ = v___y_1611_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1608_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref_known(v___x_1623_, 1);
v___x_1624_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref_known(v___x_1624_, 1);
v___y_1618_ = v___y_1611_;
goto v___jp_1617_;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_b_1609_);
lean_dec_ref(v_t_1608_);
lean_dec(v_x_1606_);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v_b_1609_);
lean_dec_ref(v_t_1608_);
lean_dec(v_x_1606_);
v_a_1633_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1623_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1623_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = l_Lean_Expr_forallE___override(v_x_1606_, v_t_1608_, v_b_1609_, v_bi_1607_);
v___x_1620_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1619_, v___y_1618_);
return v___x_1620_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1606_ = stack[0].m_obj;
uint8_t v_bi_1607_ = stack[1].m_num;
lean_object* v_t_1608_ = stack[2].m_obj;
lean_object* v_b_1609_ = stack[3].m_obj;
lean_object* v___y_1610_ = stack[4].m_obj;
lean_object* v___y_1611_ = stack[5].m_obj;
lean_object* v___y_1612_ = stack[6].m_obj;
lean_object* v___y_1613_ = stack[7].m_obj;
lean_object* v___y_1614_ = stack[8].m_obj;
lean_object* v___y_1615_ = stack[9].m_obj;
lean_object* v_res_1641_;
v_res_1641_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1606_, v_bi_1607_, v_t_1608_, v_b_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg___boxed(lean_object* v_x_1642_, lean_object* v_bi_1643_, lean_object* v_t_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_bi_boxed_1653_; lean_object* v_res_1654_; 
v_bi_boxed_1653_ = lean_unbox(v_bi_1643_);
v_res_1654_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1642_, v_bi_boxed_1653_, v_t_1644_, v_b_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1654_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(lean_object* v_x_1655_, uint8_t v_bi_1656_, lean_object* v_t_1657_, lean_object* v_b_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_x_1655_, v_bi_1656_, v_t_1657_, v_b_1658_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1655_ = stack[0].m_obj;
uint8_t v_bi_1656_ = stack[1].m_num;
lean_object* v_t_1657_ = stack[2].m_obj;
lean_object* v_b_1658_ = stack[3].m_obj;
lean_object* v___y_1659_ = stack[4].m_obj;
lean_object* v___y_1660_ = stack[5].m_obj;
lean_object* v___y_1661_ = stack[6].m_obj;
lean_object* v___y_1662_ = stack[7].m_obj;
lean_object* v___y_1663_ = stack[8].m_obj;
lean_object* v___y_1664_ = stack[9].m_obj;
lean_object* v___y_1665_ = stack[10].m_obj;
lean_object* v___y_1666_ = stack[11].m_obj;
lean_object* v___y_1667_ = stack[12].m_obj;
lean_object* v_res_1670_;
v_res_1670_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(v_x_1655_, v_bi_1656_, v_t_1657_, v_b_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
stack->m_obj
 = v_res_1670_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___boxed(lean_object* v_x_1671_, lean_object* v_bi_1672_, lean_object* v_t_1673_, lean_object* v_b_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_bi_boxed_1685_; lean_object* v_res_1686_; 
v_bi_boxed_1685_ = lean_unbox(v_bi_1672_);
v_res_1686_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(v_x_1671_, v_bi_boxed_1685_, v_t_1673_, v_b_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
return v_res_1686_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_instMonadEIO___redArg();
return v___x_1687_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(lean_object* v_msg_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v_toApplicative_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1771_; 
v___x_1703_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0);
v___x_1704_ = l_StateRefT_x27_instMonad___redArg(v___x_1703_);
v_toApplicative_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1704_, 1);
lean_dec(v_unused_1772_);
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1771_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_toApplicative_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1771_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_toFunctor_1709_; lean_object* v_toSeq_1710_; lean_object* v_toSeqLeft_1711_; lean_object* v_toSeqRight_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1769_; 
v_toFunctor_1709_ = lean_ctor_get(v_toApplicative_1705_, 0);
v_toSeq_1710_ = lean_ctor_get(v_toApplicative_1705_, 2);
v_toSeqLeft_1711_ = lean_ctor_get(v_toApplicative_1705_, 3);
v_toSeqRight_1712_ = lean_ctor_get(v_toApplicative_1705_, 4);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_toApplicative_1705_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_toApplicative_1705_, 1);
lean_dec(v_unused_1770_);
v___x_1714_ = v_toApplicative_1705_;
v_isShared_1715_ = v_isSharedCheck_1769_;
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
v_isShared_1715_ = v_isSharedCheck_1769_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1725_; 
v___f_1716_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1));
v___f_1717_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2));
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
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___f_1716_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v___f_1723_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v___f_1722_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v___f_1721_);
v___x_1725_ = v_reuseFailAlloc_1768_;
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
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___f_1717_);
v___x_1727_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v_toApplicative_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1765_; 
v___x_1728_ = l_StateRefT_x27_instMonad___redArg(v___x_1727_);
v_toApplicative_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1728_, 1);
lean_dec(v_unused_1766_);
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1765_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_toApplicative_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1765_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_toFunctor_1733_; lean_object* v_toSeq_1734_; lean_object* v_toSeqLeft_1735_; lean_object* v_toSeqRight_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1763_; 
v_toFunctor_1733_ = lean_ctor_get(v_toApplicative_1729_, 0);
v_toSeq_1734_ = lean_ctor_get(v_toApplicative_1729_, 2);
v_toSeqLeft_1735_ = lean_ctor_get(v_toApplicative_1729_, 3);
v_toSeqRight_1736_ = lean_ctor_get(v_toApplicative_1729_, 4);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_toApplicative_1729_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v_toApplicative_1729_, 1);
lean_dec(v_unused_1764_);
v___x_1738_ = v_toApplicative_1729_;
v_isShared_1739_ = v_isSharedCheck_1763_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_toSeqRight_1736_);
lean_inc(v_toSeqLeft_1735_);
lean_inc(v_toSeq_1734_);
lean_inc(v_toFunctor_1733_);
lean_dec(v_toApplicative_1729_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1763_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___f_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; lean_object* v___f_1745_; lean_object* v___f_1746_; lean_object* v___f_1747_; lean_object* v___x_1749_; 
v___f_1740_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3));
v___f_1741_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1733_);
v___f_1742_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1742_, 0, v_toFunctor_1733_);
v___f_1743_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1743_, 0, v_toFunctor_1733_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___f_1742_);
lean_ctor_set(v___x_1744_, 1, v___f_1743_);
v___f_1745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1745_, 0, v_toSeqRight_1736_);
v___f_1746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1746_, 0, v_toSeqLeft_1735_);
v___f_1747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1747_, 0, v_toSeq_1734_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 4, v___f_1745_);
lean_ctor_set(v___x_1738_, 3, v___f_1746_);
lean_ctor_set(v___x_1738_, 2, v___f_1747_);
lean_ctor_set(v___x_1738_, 1, v___f_1740_);
lean_ctor_set(v___x_1738_, 0, v___x_1744_);
v___x_1749_ = v___x_1738_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___f_1740_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v___f_1747_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v___f_1746_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___f_1745_);
v___x_1749_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___f_1741_);
lean_ctor_set(v___x_1731_, 0, v___x_1749_);
v___x_1751_ = v___x_1731_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___f_1741_);
v___x_1751_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_24914__overap_1759_; lean_object* v___x_1760_; 
v___x_1752_ = l_StateRefT_x27_instMonad___redArg(v___x_1751_);
v___x_1753_ = l_ReaderT_instMonad___redArg(v___x_1752_);
v___x_1754_ = l_StateRefT_x27_instMonad___redArg(v___x_1753_);
v___x_1755_ = l_ReaderT_instMonad___redArg(v___x_1754_);
v___x_1756_ = l_ReaderT_instMonad___redArg(v___x_1755_);
v___x_1757_ = l_Lean_instInhabitedExpr;
v___x_1758_ = l_instInhabitedOfMonad___redArg(v___x_1756_, v___x_1757_);
v___x_24914__overap_1759_ = lean_panic_fn_borrowed(v___x_1758_, v_msg_1692_);
lean_dec(v___x_1758_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
v___x_1760_ = lean_apply_10(v___x_24914__overap_1759_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, lean_box(0));
return v___x_1760_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1692_ = stack[0].m_obj;
lean_object* v___y_1693_ = stack[1].m_obj;
lean_object* v___y_1694_ = stack[2].m_obj;
lean_object* v___y_1695_ = stack[3].m_obj;
lean_object* v___y_1696_ = stack[4].m_obj;
lean_object* v___y_1697_ = stack[5].m_obj;
lean_object* v___y_1698_ = stack[6].m_obj;
lean_object* v___y_1699_ = stack[7].m_obj;
lean_object* v___y_1700_ = stack[8].m_obj;
lean_object* v___y_1701_ = stack[9].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v_msg_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___boxed(lean_object* v_msg_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v_msg_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
return v_res_1785_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1792_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__4));
v___x_1793_ = lean_unsigned_to_nat(31u);
v___x_1794_ = lean_unsigned_to_nat(160u);
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__3));
v___x_1796_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__2));
v___x_1797_ = l_mkPanicMessageWithDecl(v___x_1796_, v___x_1795_, v___x_1794_, v___x_1793_, v___x_1792_);
return v___x_1797_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpArrow(lean_object* v_e_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
uint8_t v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; uint8_t v___y_1833_; lean_object* v_p_1836_; lean_object* v_q_1837_; lean_object* v___x_1838_; 
v_p_1836_ = l_Lean_Expr_bindingDomain_x21(v_e_1804_);
v_q_1837_ = l_Lean_Expr_bindingBody_x21(v_e_1804_);
lean_inc(v_a_1813_);
lean_inc_ref(v_a_1812_);
lean_inc(v_a_1811_);
lean_inc_ref(v_a_1810_);
lean_inc(v_a_1809_);
lean_inc_ref(v_a_1808_);
lean_inc(v_a_1807_);
lean_inc_ref(v_a_1806_);
lean_inc(v_a_1805_);
lean_inc_ref(v_p_1836_);
v___x_1838_ = lean_sym_simp(v_p_1836_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1840_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
lean_inc(v_a_1813_);
lean_inc_ref(v_a_1812_);
lean_inc(v_a_1811_);
lean_inc_ref(v_a_1810_);
lean_inc(v_a_1809_);
lean_inc_ref(v_a_1808_);
lean_inc(v_a_1807_);
lean_inc_ref(v_a_1806_);
lean_inc(v_a_1805_);
lean_inc_ref(v_q_1837_);
v___x_1840_ = lean_sym_simp(v_q_1837_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_2029_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_2029_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_2029_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint8_t v___y_1846_; 
if (lean_obj_tag(v_a_1839_) == 0)
{
if (lean_obj_tag(v_a_1841_) == 0)
{
uint8_t v_contextDependent_1851_; 
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_contextDependent_1851_ = lean_ctor_get_uint8(v_a_1839_, 1);
lean_dec_ref_known(v_a_1839_, 0);
if (v_contextDependent_1851_ == 0)
{
uint8_t v_contextDependent_1852_; 
v_contextDependent_1852_ = lean_ctor_get_uint8(v_a_1841_, 1);
lean_dec_ref_known(v_a_1841_, 0);
v___y_1846_ = v_contextDependent_1852_;
goto v___jp_1845_;
}
else
{
lean_dec_ref_known(v_a_1841_, 0);
v___y_1846_ = v_contextDependent_1851_;
goto v___jp_1845_;
}
}
else
{
uint8_t v_contextDependent_1853_; lean_object* v_e_x27_1854_; lean_object* v_proof_1855_; uint8_t v_contextDependent_1856_; lean_object* v___x_1857_; 
lean_del_object(v___x_1843_);
v_contextDependent_1853_ = lean_ctor_get_uint8(v_a_1839_, 1);
lean_dec_ref_known(v_a_1839_, 0);
v_e_x27_1854_ = lean_ctor_get(v_a_1841_, 0);
lean_inc_ref(v_e_x27_1854_);
v_proof_1855_ = lean_ctor_get(v_a_1841_, 1);
lean_inc_ref(v_proof_1855_);
v_contextDependent_1856_ = lean_ctor_get_uint8(v_a_1841_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1841_, 2);
lean_inc_ref(v_p_1836_);
v___x_1857_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1836_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
lean_inc_ref(v_q_1837_);
v___x_1859_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1837_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v_a_1862_; lean_object* v___y_1871_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
if (lean_obj_tag(v_e_1804_) == 7)
{
lean_object* v_binderName_1881_; lean_object* v_binderType_1882_; lean_object* v_body_1883_; uint8_t v_binderInfo_1884_; size_t v___x_1885_; size_t v___x_1886_; uint8_t v___x_1887_; 
v_binderName_1881_ = lean_ctor_get(v_e_1804_, 0);
v_binderType_1882_ = lean_ctor_get(v_e_1804_, 1);
v_body_1883_ = lean_ctor_get(v_e_1804_, 2);
v_binderInfo_1884_ = lean_ctor_get_uint8(v_e_1804_, sizeof(void*)*3 + 8);
v___x_1885_ = lean_ptr_addr(v_binderType_1882_);
v___x_1886_ = lean_ptr_addr(v_p_1836_);
v___x_1887_ = lean_usize_dec_eq(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_inc(v_binderName_1881_);
lean_dec_ref_known(v_e_1804_, 3);
lean_inc_ref(v_e_x27_1854_);
lean_inc_ref(v_p_1836_);
v___x_1888_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1881_, v_binderInfo_1884_, v_p_1836_, v_e_x27_1854_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1871_ = v___x_1888_;
goto v___jp_1870_;
}
else
{
size_t v___x_1889_; size_t v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = lean_ptr_addr(v_body_1883_);
v___x_1890_ = lean_ptr_addr(v_e_x27_1854_);
v___x_1891_ = lean_usize_dec_eq(v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
lean_inc(v_binderName_1881_);
lean_dec_ref_known(v_e_1804_, 3);
lean_inc_ref(v_e_x27_1854_);
lean_inc_ref(v_p_1836_);
v___x_1892_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1881_, v_binderInfo_1884_, v_p_1836_, v_e_x27_1854_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1871_ = v___x_1892_;
goto v___jp_1870_;
}
else
{
v_a_1862_ = v_e_1804_;
goto v___jp_1861_;
}
}
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v_e_1804_);
v___x_1893_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1894_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1893_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1871_ = v___x_1894_;
goto v___jp_1870_;
}
v___jp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1863_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__1));
v___x_1864_ = lean_box(0);
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v_a_1860_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v_a_1858_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_mkConst(v___x_1863_, v___x_1866_);
v___x_1868_ = l_Lean_mkApp4(v___x_1867_, v_p_1836_, v_q_1837_, v_e_x27_1854_, v_proof_1855_);
v___x_1869_ = 0;
if (v_contextDependent_1853_ == 0)
{
v___y_1816_ = v___x_1869_;
v___y_1817_ = v_a_1862_;
v___y_1818_ = v___x_1868_;
v___y_1819_ = v_contextDependent_1856_;
goto v___jp_1815_;
}
else
{
v___y_1816_ = v___x_1869_;
v___y_1817_ = v_a_1862_;
v___y_1818_ = v___x_1868_;
v___y_1819_ = v_contextDependent_1853_;
goto v___jp_1815_;
}
}
v___jp_1870_:
{
if (lean_obj_tag(v___y_1871_) == 0)
{
lean_object* v_a_1872_; 
v_a_1872_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___y_1871_, 1);
v_a_1862_ = v_a_1872_;
goto v___jp_1861_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1860_);
lean_dec(v_a_1858_);
lean_dec_ref(v_proof_1855_);
lean_dec_ref(v_e_x27_1854_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
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
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1858_);
lean_dec_ref(v_proof_1855_);
lean_dec_ref(v_e_x27_1854_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_a_1895_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1859_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1859_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v_proof_1855_);
lean_dec_ref(v_e_x27_1854_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_a_1903_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1857_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1857_);
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
lean_del_object(v___x_1843_);
if (lean_obj_tag(v_a_1841_) == 0)
{
lean_object* v_e_x27_1911_; lean_object* v_proof_1912_; uint8_t v_contextDependent_1913_; uint8_t v_contextDependent_1914_; lean_object* v___x_1915_; 
v_e_x27_1911_ = lean_ctor_get(v_a_1839_, 0);
lean_inc_ref(v_e_x27_1911_);
v_proof_1912_ = lean_ctor_get(v_a_1839_, 1);
lean_inc_ref(v_proof_1912_);
v_contextDependent_1913_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1839_, 2);
v_contextDependent_1914_ = lean_ctor_get_uint8(v_a_1841_, 1);
lean_dec_ref_known(v_a_1841_, 0);
lean_inc_ref(v_p_1836_);
v___x_1915_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1836_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
lean_inc_ref(v_q_1837_);
v___x_1917_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1837_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_a_1920_; lean_object* v___y_1929_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
if (lean_obj_tag(v_e_1804_) == 7)
{
lean_object* v_binderName_1939_; lean_object* v_binderType_1940_; lean_object* v_body_1941_; uint8_t v_binderInfo_1942_; size_t v___x_1943_; size_t v___x_1944_; uint8_t v___x_1945_; 
v_binderName_1939_ = lean_ctor_get(v_e_1804_, 0);
v_binderType_1940_ = lean_ctor_get(v_e_1804_, 1);
v_body_1941_ = lean_ctor_get(v_e_1804_, 2);
v_binderInfo_1942_ = lean_ctor_get_uint8(v_e_1804_, sizeof(void*)*3 + 8);
v___x_1943_ = lean_ptr_addr(v_binderType_1940_);
v___x_1944_ = lean_ptr_addr(v_e_x27_1911_);
v___x_1945_ = lean_usize_dec_eq(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_inc(v_binderName_1939_);
lean_dec_ref_known(v_e_1804_, 3);
lean_inc_ref(v_q_1837_);
lean_inc_ref(v_e_x27_1911_);
v___x_1946_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1939_, v_binderInfo_1942_, v_e_x27_1911_, v_q_1837_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1929_ = v___x_1946_;
goto v___jp_1928_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = lean_ptr_addr(v_body_1941_);
v___x_1948_ = lean_ptr_addr(v_q_1837_);
v___x_1949_ = lean_usize_dec_eq(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_inc(v_binderName_1939_);
lean_dec_ref_known(v_e_1804_, 3);
lean_inc_ref(v_q_1837_);
lean_inc_ref(v_e_x27_1911_);
v___x_1950_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1939_, v_binderInfo_1942_, v_e_x27_1911_, v_q_1837_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1929_ = v___x_1950_;
goto v___jp_1928_;
}
else
{
v_a_1920_ = v_e_1804_;
goto v___jp_1919_;
}
}
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec_ref(v_e_1804_);
v___x_1951_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1952_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1951_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1929_ = v___x_1952_;
goto v___jp_1928_;
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__7));
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1918_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1916_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Lean_mkConst(v___x_1921_, v___x_1924_);
v___x_1926_ = l_Lean_mkApp4(v___x_1925_, v_p_1836_, v_e_x27_1911_, v_q_1837_, v_proof_1912_);
v___x_1927_ = 0;
if (v_contextDependent_1913_ == 0)
{
v___y_1823_ = v___x_1926_;
v___y_1824_ = v___x_1927_;
v___y_1825_ = v_a_1920_;
v___y_1826_ = v_contextDependent_1914_;
goto v___jp_1822_;
}
else
{
v___y_1823_ = v___x_1926_;
v___y_1824_ = v___x_1927_;
v___y_1825_ = v_a_1920_;
v___y_1826_ = v_contextDependent_1913_;
goto v___jp_1822_;
}
}
v___jp_1928_:
{
if (lean_obj_tag(v___y_1929_) == 0)
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___y_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___y_1929_, 1);
v_a_1920_ = v_a_1930_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1918_);
lean_dec(v_a_1916_);
lean_dec_ref(v_proof_1912_);
lean_dec_ref(v_e_x27_1911_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
v_a_1931_ = lean_ctor_get(v___y_1929_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___y_1929_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___y_1929_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___y_1929_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1916_);
lean_dec_ref(v_proof_1912_);
lean_dec_ref(v_e_x27_1911_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_a_1953_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1917_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1917_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_proof_1912_);
lean_dec_ref(v_e_x27_1911_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_a_1961_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1915_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1915_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_e_x27_1969_; lean_object* v_proof_1970_; uint8_t v_contextDependent_1971_; lean_object* v_e_x27_1972_; lean_object* v_proof_1973_; uint8_t v_contextDependent_1974_; lean_object* v___x_1975_; 
v_e_x27_1969_ = lean_ctor_get(v_a_1839_, 0);
lean_inc_ref(v_e_x27_1969_);
v_proof_1970_ = lean_ctor_get(v_a_1839_, 1);
lean_inc_ref(v_proof_1970_);
v_contextDependent_1971_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1839_, 2);
v_e_x27_1972_ = lean_ctor_get(v_a_1841_, 0);
lean_inc_ref(v_e_x27_1972_);
v_proof_1973_ = lean_ctor_get(v_a_1841_, 1);
lean_inc_ref(v_proof_1973_);
v_contextDependent_1974_ = lean_ctor_get_uint8(v_a_1841_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1841_, 2);
lean_inc_ref(v_p_1836_);
v___x_1975_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1836_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
lean_inc_ref(v_q_1837_);
v___x_1977_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1837_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v_a_1980_; lean_object* v___y_1989_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
if (lean_obj_tag(v_e_1804_) == 7)
{
lean_object* v_binderName_1999_; lean_object* v_binderType_2000_; lean_object* v_body_2001_; uint8_t v_binderInfo_2002_; size_t v___x_2003_; size_t v___x_2004_; uint8_t v___x_2005_; 
v_binderName_1999_ = lean_ctor_get(v_e_1804_, 0);
v_binderType_2000_ = lean_ctor_get(v_e_1804_, 1);
v_body_2001_ = lean_ctor_get(v_e_1804_, 2);
v_binderInfo_2002_ = lean_ctor_get_uint8(v_e_1804_, sizeof(void*)*3 + 8);
v___x_2003_ = lean_ptr_addr(v_binderType_2000_);
v___x_2004_ = lean_ptr_addr(v_e_x27_1969_);
v___x_2005_ = lean_usize_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_inc(v_binderName_1999_);
lean_dec_ref_known(v_e_1804_, 3);
lean_inc_ref(v_e_x27_1972_);
lean_inc_ref(v_e_x27_1969_);
v___x_2006_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1999_, v_binderInfo_2002_, v_e_x27_1969_, v_e_x27_1972_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1989_ = v___x_2006_;
goto v___jp_1988_;
}
else
{
size_t v___x_2007_; size_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = lean_ptr_addr(v_body_2001_);
v___x_2008_ = lean_ptr_addr(v_e_x27_1972_);
v___x_2009_ = lean_usize_dec_eq(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_inc(v_binderName_1999_);
lean_dec_ref_known(v_e_1804_, 3);
lean_inc_ref(v_e_x27_1972_);
lean_inc_ref(v_e_x27_1969_);
v___x_2010_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1999_, v_binderInfo_2002_, v_e_x27_1969_, v_e_x27_1972_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1989_ = v___x_2010_;
goto v___jp_1988_;
}
else
{
v_a_1980_ = v_e_1804_;
goto v___jp_1979_;
}
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec_ref(v_e_1804_);
v___x_2011_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_2012_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_2011_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v___y_1989_ = v___x_2012_;
goto v___jp_1988_;
}
v___jp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__9));
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_a_1978_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1976_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_mkConst(v___x_1981_, v___x_1984_);
v___x_1986_ = l_Lean_mkApp6(v___x_1985_, v_p_1836_, v_e_x27_1969_, v_q_1837_, v_e_x27_1972_, v_proof_1970_, v_proof_1973_);
v___x_1987_ = 0;
if (v_contextDependent_1971_ == 0)
{
v___y_1830_ = v___x_1986_;
v___y_1831_ = v_a_1980_;
v___y_1832_ = v___x_1987_;
v___y_1833_ = v_contextDependent_1974_;
goto v___jp_1829_;
}
else
{
v___y_1830_ = v___x_1986_;
v___y_1831_ = v_a_1980_;
v___y_1832_ = v___x_1987_;
v___y_1833_ = v_contextDependent_1971_;
goto v___jp_1829_;
}
}
v___jp_1988_:
{
if (lean_obj_tag(v___y_1989_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___y_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___y_1989_, 1);
v_a_1980_ = v_a_1990_;
goto v___jp_1979_;
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_a_1978_);
lean_dec(v_a_1976_);
lean_dec_ref(v_proof_1973_);
lean_dec_ref(v_e_x27_1972_);
lean_dec_ref(v_proof_1970_);
lean_dec_ref(v_e_x27_1969_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
v_a_1991_ = lean_ctor_get(v___y_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___y_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___y_1989_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___y_1989_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_a_1976_);
lean_dec_ref(v_proof_1973_);
lean_dec_ref(v_e_x27_1972_);
lean_dec_ref(v_proof_1970_);
lean_dec_ref(v_e_x27_1969_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_a_2013_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1977_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1977_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v_proof_1973_);
lean_dec_ref(v_e_x27_1972_);
lean_dec_ref(v_proof_1970_);
lean_dec_ref(v_e_x27_1969_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
v_a_2021_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1975_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1975_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
v___jp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1846_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1847_);
v___x_1849_ = v___x_1843_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_dec(v_a_1839_);
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
return v___x_1840_;
}
}
else
{
lean_dec_ref(v_q_1837_);
lean_dec_ref(v_p_1836_);
lean_dec_ref(v_e_1804_);
return v___x_1838_;
}
v___jp_1815_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1820_, 0, v___y_1817_);
lean_ctor_set(v___x_1820_, 1, v___y_1818_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*2, v___y_1816_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*2 + 1, v___y_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
v___jp_1822_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1827_, 0, v___y_1825_);
lean_ctor_set(v___x_1827_, 1, v___y_1823_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*2, v___y_1824_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*2 + 1, v___y_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
v___jp_1829_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1834_, 0, v___y_1831_);
lean_ctor_set(v___x_1834_, 1, v___y_1830_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*2, v___y_1832_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*2 + 1, v___y_1833_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpArrow_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1804_ = stack[0].m_obj;
lean_object* v_a_1805_ = stack[1].m_obj;
lean_object* v_a_1806_ = stack[2].m_obj;
lean_object* v_a_1807_ = stack[3].m_obj;
lean_object* v_a_1808_ = stack[4].m_obj;
lean_object* v_a_1809_ = stack[5].m_obj;
lean_object* v_a_1810_ = stack[6].m_obj;
lean_object* v_a_1811_ = stack[7].m_obj;
lean_object* v_a_1812_ = stack[8].m_obj;
lean_object* v_a_1813_ = stack[9].m_obj;
lean_object* v_res_2030_;
v_res_2030_ = l_Lean_Meta_Sym_Simp_simpArrow(v_e_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
stack->m_obj
 = v_res_2030_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow___boxed(lean_object* v_e_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Meta_Sym_Simp_simpArrow(v_e_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
return v_res_2042_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(lean_object* v_simpBody_2043_, lean_object* v_xs_2044_, lean_object* v_b_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; 
lean_inc(v_a_2054_);
lean_inc_ref(v_a_2053_);
lean_inc(v_a_2052_);
lean_inc_ref(v_a_2051_);
lean_inc(v_a_2050_);
lean_inc_ref(v_a_2049_);
lean_inc(v_a_2048_);
lean_inc_ref(v_a_2047_);
lean_inc(v_a_2046_);
lean_inc_ref(v_b_2045_);
v___x_2056_ = lean_apply_11(v_simpBody_2043_, v_b_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, lean_box(0));
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2147_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2147_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2147_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
if (lean_obj_tag(v_a_2057_) == 0)
{
uint8_t v_contextDependent_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_xs_2044_);
v_contextDependent_2061_ = lean_ctor_get_uint8(v_a_2057_, 1);
lean_dec_ref_known(v_a_2057_, 0);
v___x_2062_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2061_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2062_);
v___x_2064_ = v___x_2059_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
else
{
lean_object* v_e_x27_2066_; lean_object* v_proof_2067_; uint8_t v_contextDependent_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_2059_);
v_e_x27_2066_ = lean_ctor_get(v_a_2057_, 0);
v_proof_2067_ = lean_ctor_get(v_a_2057_, 1);
v_contextDependent_2068_ = lean_ctor_get_uint8(v_a_2057_, sizeof(void*)*2 + 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2057_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2070_ = v_a_2057_;
v_isShared_2071_ = v_isSharedCheck_2146_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_proof_2067_);
lean_inc(v_e_x27_2066_);
lean_dec(v_a_2057_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2146_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2072_ = 0;
v___x_2073_ = 1;
v___x_2074_ = 1;
v___x_2075_ = l_Lean_Meta_mkLambdaFVars(v_xs_2044_, v_proof_2067_, v___x_2072_, v___x_2073_, v___x_2072_, v___x_2073_, v___x_2074_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
lean_inc_ref(v_e_x27_2066_);
v___x_2077_ = l_Lean_Meta_mkForallFVars(v_xs_2044_, v_e_x27_2066_, v___x_2072_, v___x_2073_, v___x_2073_, v___x_2074_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Meta_Sym_shareCommon(v_a_2078_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 1);
lean_inc_ref(v_xs_2044_);
v___x_2081_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_2044_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = l_Lean_Meta_mkLambdaFVars(v_xs_2044_, v_b_2045_, v___x_2072_, v___x_2073_, v___x_2072_, v___x_2073_, v___x_2074_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = l_Lean_Meta_mkLambdaFVars(v_xs_2044_, v_e_x27_2066_, v___x_2072_, v___x_2073_, v___x_2072_, v___x_2073_, v___x_2074_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
lean_dec_ref(v_xs_2044_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2097_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2097_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2097_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = l_Lean_mkApp3(v_a_2082_, v_a_2084_, v_a_2086_, v_a_2076_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2090_);
lean_ctor_set(v___x_2070_, 0, v_a_2080_);
v___x_2092_ = v___x_2070_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2080_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2096_, sizeof(void*)*2 + 1, v_contextDependent_2068_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*2, v___x_2072_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2092_);
v___x_2094_ = v___x_2088_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_a_2084_);
lean_dec(v_a_2082_);
lean_dec(v_a_2080_);
lean_dec(v_a_2076_);
lean_del_object(v___x_2070_);
v_a_2098_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2085_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2085_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2082_);
lean_dec(v_a_2080_);
lean_dec(v_a_2076_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_e_x27_2066_);
lean_dec_ref(v_xs_2044_);
v_a_2106_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2083_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2083_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_a_2080_);
lean_dec(v_a_2076_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_e_x27_2066_);
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_xs_2044_);
v_a_2114_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2081_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2081_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_a_2076_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_e_x27_2066_);
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_xs_2044_);
v_a_2122_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2079_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2079_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2076_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_e_x27_2066_);
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_xs_2044_);
v_a_2130_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2077_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2077_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2070_);
lean_dec_ref(v_e_x27_2066_);
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_xs_2044_);
v_a_2138_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2075_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2075_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_xs_2044_);
return v___x_2056_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_2043_ = stack[0].m_obj;
lean_object* v_xs_2044_ = stack[1].m_obj;
lean_object* v_b_2045_ = stack[2].m_obj;
lean_object* v_a_2046_ = stack[3].m_obj;
lean_object* v_a_2047_ = stack[4].m_obj;
lean_object* v_a_2048_ = stack[5].m_obj;
lean_object* v_a_2049_ = stack[6].m_obj;
lean_object* v_a_2050_ = stack[7].m_obj;
lean_object* v_a_2051_ = stack[8].m_obj;
lean_object* v_a_2052_ = stack[9].m_obj;
lean_object* v_a_2053_ = stack[10].m_obj;
lean_object* v_a_2054_ = stack[11].m_obj;
lean_object* v_res_2148_;
v_res_2148_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2043_, v_xs_2044_, v_b_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
stack->m_obj
 = v_res_2148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main___boxed(lean_object* v_simpBody_2149_, lean_object* v_xs_2150_, lean_object* v_b_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2149_, v_xs_2150_, v_b_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(lean_object* v_e_2163_, lean_object* v_n_2164_){
_start:
{
if (lean_obj_tag(v_e_2163_) == 7)
{
lean_object* v_body_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_body_2165_ = lean_ctor_get(v_e_2163_, 2);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_expr_has_loose_bvar(v_body_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
return v_n_2164_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_add(v_n_2164_, v___x_2168_);
lean_dec(v_n_2164_);
v_e_2163_ = v_body_2165_;
v_n_2164_ = v___x_2169_;
goto _start;
}
}
else
{
return v_n_2164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize___boxed(lean_object* v_e_2171_, lean_object* v_n_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v_e_2171_, v_n_2172_);
lean_dec_ref(v_e_2171_);
return v_res_2173_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(lean_object* v_k_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v_b_2180_, lean_object* v_c_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
lean_inc(v___y_2185_);
lean_inc_ref(v___y_2184_);
lean_inc(v___y_2183_);
lean_inc_ref(v___y_2182_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc_ref(v___y_2176_);
lean_inc(v___y_2175_);
v___x_2187_ = lean_apply_12(v_k_2174_, v_b_2180_, v_c_2181_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, lean_box(0));
return v___x_2187_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2174_ = stack[0].m_obj;
lean_object* v___y_2175_ = stack[1].m_obj;
lean_object* v___y_2176_ = stack[2].m_obj;
lean_object* v___y_2177_ = stack[3].m_obj;
lean_object* v___y_2178_ = stack[4].m_obj;
lean_object* v___y_2179_ = stack[5].m_obj;
lean_object* v_b_2180_ = stack[6].m_obj;
lean_object* v_c_2181_ = stack[7].m_obj;
lean_object* v___y_2182_ = stack[8].m_obj;
lean_object* v___y_2183_ = stack[9].m_obj;
lean_object* v___y_2184_ = stack[10].m_obj;
lean_object* v___y_2185_ = stack[11].m_obj;
lean_object* v_res_2188_;
v_res_2188_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(v_k_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v_b_2180_, v_c_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
stack->m_obj
 = v_res_2188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v_b_2195_, lean_object* v_c_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(v_k_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v_b_2195_, v_c_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
return v_res_2202_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(lean_object* v_type_2203_, lean_object* v_maxFVars_x3f_2204_, lean_object* v_k_2205_, uint8_t v_cleanupAnnotations_2206_, uint8_t v_whnfType_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___f_2218_; lean_object* v___x_2219_; 
lean_inc(v___y_2212_);
lean_inc_ref(v___y_2211_);
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
lean_inc(v___y_2208_);
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2218_, 0, v_k_2205_);
lean_closure_set(v___f_2218_, 1, v___y_2208_);
lean_closure_set(v___f_2218_, 2, v___y_2209_);
lean_closure_set(v___f_2218_, 3, v___y_2210_);
lean_closure_set(v___f_2218_, 4, v___y_2211_);
lean_closure_set(v___f_2218_, 5, v___y_2212_);
v___x_2219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2203_, v_maxFVars_x3f_2204_, v___f_2218_, v_cleanupAnnotations_2206_, v_whnfType_2207_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2219_) == 0)
{
return v___x_2219_;
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2203_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_2204_ = stack[1].m_obj;
lean_object* v_k_2205_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2206_ = stack[3].m_num;
uint8_t v_whnfType_2207_ = stack[4].m_num;
lean_object* v___y_2208_ = stack[5].m_obj;
lean_object* v___y_2209_ = stack[6].m_obj;
lean_object* v___y_2210_ = stack[7].m_obj;
lean_object* v___y_2211_ = stack[8].m_obj;
lean_object* v___y_2212_ = stack[9].m_obj;
lean_object* v___y_2213_ = stack[10].m_obj;
lean_object* v___y_2214_ = stack[11].m_obj;
lean_object* v___y_2215_ = stack[12].m_obj;
lean_object* v___y_2216_ = stack[13].m_obj;
lean_object* v_res_2228_;
v_res_2228_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2203_, v_maxFVars_x3f_2204_, v_k_2205_, v_cleanupAnnotations_2206_, v_whnfType_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
stack->m_obj
 = v_res_2228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___boxed(lean_object* v_type_2229_, lean_object* v_maxFVars_x3f_2230_, lean_object* v_k_2231_, lean_object* v_cleanupAnnotations_2232_, lean_object* v_whnfType_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2244_; uint8_t v_whnfType_boxed_2245_; lean_object* v_res_2246_; 
v_cleanupAnnotations_boxed_2244_ = lean_unbox(v_cleanupAnnotations_2232_);
v_whnfType_boxed_2245_ = lean_unbox(v_whnfType_2233_);
v_res_2246_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2229_, v_maxFVars_x3f_2230_, v_k_2231_, v_cleanupAnnotations_boxed_2244_, v_whnfType_boxed_2245_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
return v_res_2246_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(lean_object* v_00_u03b1_2247_, lean_object* v_type_2248_, lean_object* v_maxFVars_x3f_2249_, lean_object* v_k_2250_, uint8_t v_cleanupAnnotations_2251_, uint8_t v_whnfType_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_2248_, v_maxFVars_x3f_2249_, v_k_2250_, v_cleanupAnnotations_2251_, v_whnfType_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2248_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_2249_ = stack[2].m_obj;
lean_object* v_k_2250_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_2251_ = stack[4].m_num;
uint8_t v_whnfType_2252_ = stack[5].m_num;
lean_object* v___y_2253_ = stack[6].m_obj;
lean_object* v___y_2254_ = stack[7].m_obj;
lean_object* v___y_2255_ = stack[8].m_obj;
lean_object* v___y_2256_ = stack[9].m_obj;
lean_object* v___y_2257_ = stack[10].m_obj;
lean_object* v___y_2258_ = stack[11].m_obj;
lean_object* v___y_2259_ = stack[12].m_obj;
lean_object* v___y_2260_ = stack[13].m_obj;
lean_object* v___y_2261_ = stack[14].m_obj;
lean_object* v_res_2264_;
v_res_2264_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(lean_box(0), v_type_2248_, v_maxFVars_x3f_2249_, v_k_2250_, v_cleanupAnnotations_2251_, v_whnfType_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
stack->m_obj
 = v_res_2264_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___boxed(lean_object* v_00_u03b1_2265_, lean_object* v_type_2266_, lean_object* v_maxFVars_x3f_2267_, lean_object* v_k_2268_, lean_object* v_cleanupAnnotations_2269_, lean_object* v_whnfType_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2281_; uint8_t v_whnfType_boxed_2282_; lean_object* v_res_2283_; 
v_cleanupAnnotations_boxed_2281_ = lean_unbox(v_cleanupAnnotations_2269_);
v_whnfType_boxed_2282_ = lean_unbox(v_whnfType_2270_);
v_res_2283_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(v_00_u03b1_2265_, v_type_2266_, v_maxFVars_x3f_2267_, v_k_2268_, v_cleanupAnnotations_boxed_2281_, v_whnfType_boxed_2282_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
return v_res_2283_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(lean_object* v___y_2284_, lean_object* v_transientCache_2285_, lean_object* v_funext_2286_, lean_object* v_a_x3f_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v_numSteps_2290_; lean_object* v_persistentCache_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2301_; 
v___x_2289_ = lean_st_ref_take(v___y_2284_);
v_numSteps_2290_ = lean_ctor_get(v___x_2289_, 0);
v_persistentCache_2291_ = lean_ctor_get(v___x_2289_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; lean_object* v_unused_2303_; 
v_unused_2302_ = lean_ctor_get(v___x_2289_, 3);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v___x_2289_, 2);
lean_dec(v_unused_2303_);
v___x_2293_ = v___x_2289_;
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_persistentCache_2291_);
lean_inc(v_numSteps_2290_);
lean_dec(v___x_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = lean_box(0);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 3, v_funext_2286_);
lean_ctor_set(v___x_2293_, 2, v_transientCache_2285_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_numSteps_2290_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_persistentCache_2291_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_transientCache_2285_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_funext_2286_);
v___x_2297_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_st_ref_put(v___y_2284_, v___x_2297_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2295_);
return v___x_2299_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2284_ = stack[0].m_obj;
lean_object* v_transientCache_2285_ = stack[1].m_obj;
lean_object* v_funext_2286_ = stack[2].m_obj;
lean_object* v_a_x3f_2287_ = stack[3].m_obj;
lean_object* v_res_2304_;
v_res_2304_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2284_, v_transientCache_2285_, v_funext_2286_, v_a_x3f_2287_);
stack->m_obj
 = v_res_2304_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0___boxed(lean_object* v___y_2305_, lean_object* v_transientCache_2306_, lean_object* v_funext_2307_, lean_object* v_a_x3f_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2305_, v_transientCache_2306_, v_funext_2307_, v_a_x3f_2308_);
lean_dec(v_a_x3f_2308_);
lean_dec(v___y_2305_);
return v_res_2310_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(lean_object* v_simpBody_2311_, lean_object* v_xs_2312_, lean_object* v_b_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; lean_object* v_transientCache_2325_; lean_object* v___x_2326_; lean_object* v_funext_2327_; lean_object* v_a_2329_; lean_object* v___x_2340_; 
v___x_2324_ = lean_st_ref_get(v___y_2316_);
v_transientCache_2325_ = lean_ctor_get(v___x_2324_, 2);
lean_inc_ref(v_transientCache_2325_);
lean_dec(v___x_2324_);
v___x_2326_ = lean_st_ref_get(v___y_2316_);
v_funext_2327_ = lean_ctor_get(v___x_2326_, 3);
lean_inc_ref(v_funext_2327_);
lean_dec(v___x_2326_);
v___x_2340_ = l_Lean_Meta_Sym_shareCommon(v_b_2313_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_2311_, v_xs_2312_, v_a_2341_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
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
lean_object* v___x_2348_; 
lean_inc(v_a_2343_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 1);
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v___x_2349_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2316_, v_transientCache_2325_, v_funext_2327_, v___x_2348_);
lean_dec_ref(v___x_2348_);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v___x_2349_, 0);
lean_dec(v_unused_2357_);
v___x_2351_ = v___x_2349_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v___x_2349_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_a_2343_);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2343_);
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
}
else
{
lean_object* v_a_2360_; 
v_a_2360_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2342_, 1);
v_a_2329_ = v_a_2360_;
goto v___jp_2328_;
}
}
else
{
lean_object* v_a_2361_; 
lean_dec_ref(v_xs_2312_);
lean_dec_ref(v_simpBody_2311_);
v_a_2361_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2340_, 1);
v_a_2329_ = v_a_2361_;
goto v___jp_2328_;
}
v___jp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v___x_2330_ = lean_box(0);
v___x_2331_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(v___y_2316_, v_transientCache_2325_, v_funext_2327_, v___x_2330_);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2331_, 0);
lean_dec(v_unused_2339_);
v___x_2333_ = v___x_2331_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v___x_2331_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 1);
lean_ctor_set(v___x_2333_, 0, v_a_2329_);
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2329_);
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
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_2311_ = stack[0].m_obj;
lean_object* v_xs_2312_ = stack[1].m_obj;
lean_object* v_b_2313_ = stack[2].m_obj;
lean_object* v___y_2314_ = stack[3].m_obj;
lean_object* v___y_2315_ = stack[4].m_obj;
lean_object* v___y_2316_ = stack[5].m_obj;
lean_object* v___y_2317_ = stack[6].m_obj;
lean_object* v___y_2318_ = stack[7].m_obj;
lean_object* v___y_2319_ = stack[8].m_obj;
lean_object* v___y_2320_ = stack[9].m_obj;
lean_object* v___y_2321_ = stack[10].m_obj;
lean_object* v___y_2322_ = stack[11].m_obj;
lean_object* v_res_2362_;
v_res_2362_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(v_simpBody_2311_, v_xs_2312_, v_b_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
stack->m_obj
 = v_res_2362_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed(lean_object* v_simpBody_2363_, lean_object* v_xs_2364_, lean_object* v_b_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(v_simpBody_2363_, v_xs_2364_, v_b_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
return v_res_2376_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object* v_simpArrow_2377_, lean_object* v_simpBody_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
uint8_t v___x_2390_; 
v___x_2390_ = l_Lean_Expr_isArrow(v_e_2379_);
if (v___x_2390_ == 0)
{
lean_object* v___f_2391_; lean_object* v___x_2392_; 
lean_dec_ref(v_simpArrow_2377_);
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed), 13, 1);
lean_closure_set(v___f_2391_, 0, v_simpBody_2378_);
lean_inc_ref(v_e_2379_);
v___x_2392_ = l_Lean_Meta_isProp(v_e_2379_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2409_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2409_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2409_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_unbox(v_a_2393_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; uint8_t v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2402_; 
lean_dec_ref(v___f_2391_);
lean_dec_ref(v_e_2379_);
v___x_2398_ = lean_alloc_ctor(0, 0, 2);
v___x_2399_ = lean_unbox(v_a_2393_);
lean_ctor_set_uint8(v___x_2398_, 0, v___x_2399_);
v___x_2400_ = lean_unbox(v_a_2393_);
lean_dec(v_a_2393_);
lean_ctor_set_uint8(v___x_2398_, 1, v___x_2400_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2398_);
v___x_2402_ = v___x_2395_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2398_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_del_object(v___x_2395_);
lean_dec(v_a_2393_);
v___x_2404_ = l_Lean_Expr_bindingBody_x21(v_e_2379_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v___x_2404_, v___x_2405_);
lean_dec_ref(v___x_2404_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
v___x_2408_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_e_2379_, v___x_2407_, v___f_2391_, v___x_2390_, v___x_2390_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
return v___x_2408_;
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___f_2391_);
lean_dec_ref(v_e_2379_);
v_a_2410_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2392_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2392_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v___x_2418_; 
lean_dec_ref(v_simpBody_2378_);
lean_inc(v_a_2388_);
lean_inc_ref(v_a_2387_);
lean_inc(v_a_2386_);
lean_inc_ref(v_a_2385_);
lean_inc(v_a_2384_);
lean_inc_ref(v_a_2383_);
lean_inc(v_a_2382_);
lean_inc_ref(v_a_2381_);
lean_inc(v_a_2380_);
v___x_2418_ = lean_apply_11(v_simpArrow_2377_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, lean_box(0));
return v___x_2418_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpForall_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpArrow_2377_ = stack[0].m_obj;
lean_object* v_simpBody_2378_ = stack[1].m_obj;
lean_object* v_e_2379_ = stack[2].m_obj;
lean_object* v_a_2380_ = stack[3].m_obj;
lean_object* v_a_2381_ = stack[4].m_obj;
lean_object* v_a_2382_ = stack[5].m_obj;
lean_object* v_a_2383_ = stack[6].m_obj;
lean_object* v_a_2384_ = stack[7].m_obj;
lean_object* v_a_2385_ = stack[8].m_obj;
lean_object* v_a_2386_ = stack[9].m_obj;
lean_object* v_a_2387_ = stack[10].m_obj;
lean_object* v_a_2388_ = stack[11].m_obj;
lean_object* v_res_2419_;
v_res_2419_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v_simpArrow_2377_, v_simpBody_2378_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
stack->m_obj
 = v_res_2419_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object* v_simpArrow_2420_, lean_object* v_simpBody_2421_, lean_object* v_e_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v_simpArrow_2420_, v_simpBody_2421_, v_e_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
return v_res_2433_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object* v_e_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__0));
v___x_2448_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__1));
v___x_2449_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v___x_2447_, v___x_2448_, v_e_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
return v___x_2449_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2436_ = stack[0].m_obj;
lean_object* v_a_2437_ = stack[1].m_obj;
lean_object* v_a_2438_ = stack[2].m_obj;
lean_object* v_a_2439_ = stack[3].m_obj;
lean_object* v_a_2440_ = stack[4].m_obj;
lean_object* v_a_2441_ = stack[5].m_obj;
lean_object* v_a_2442_ = stack[6].m_obj;
lean_object* v_a_2443_ = stack[7].m_obj;
lean_object* v_a_2444_ = stack[8].m_obj;
lean_object* v_a_2445_ = stack[9].m_obj;
lean_object* v_res_2450_;
v_res_2450_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
stack->m_obj
 = v_res_2450_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object* v_e_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
return v_res_2462_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
