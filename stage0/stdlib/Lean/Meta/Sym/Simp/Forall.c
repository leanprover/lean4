// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Forall
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Util import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AbstractS
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_instantiateS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "p'"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 84, 71, 254, 8, 249, 37, 40)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 208, 133, 57, 225, 251, 103, 73)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "arrow_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 43, 230, 22, 134, 52, 48, 206)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_congr_left"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 72, 118, 56, 86, 132, 84, 122)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "arrow_congr_right"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 119, 110, 93, 174, 252, 11, 102)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "arrow_true_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value),LEAN_SCALAR_PTR_LITERAL(26, 244, 117, 192, 201, 44, 53, 165)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrow_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value),LEAN_SCALAR_PTR_LITERAL(253, 60, 249, 93, 169, 23, 87, 100)}};
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
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "substr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 253, 121, 186, 205, 175, 35, 173)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "forall_prop_congr_dom"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 60, 41, 113, 120, 179, 141, 84)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "forall_prop_domain_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 216, 34, 74, 208, 79, 94, 130)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.Sym.Simp.Forall"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Meta.Sym.Simp.Forall.0.Lean.Meta.Sym.Simp.simpForall'.simpPropDomain"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_Simp_simpForall_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpForall_x27___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "exists_prop_congr_dom"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 186, 167, 124, 20, 150, 71, 194)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpArrow___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpForall___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpForall___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpForall___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(lean_object* v___x_9_, lean_object* v_a_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v_xs_13_, lean_object* v___x_14_, lean_object* v_a_15_, lean_object* v___x_16_, lean_object* v_a_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_prop_20_, uint8_t v___x_21_, uint8_t v___x_22_, uint8_t v___x_23_, lean_object* v___x_24_, lean_object* v_p_25_, lean_object* v_q_26_, lean_object* v_h_27_, lean_object* v___x_28_, lean_object* v___x_29_, lean_object* v___x_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v_p_x27_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_40_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0));
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
v___x_59_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1));
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
v___x_63_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2));
v___x_64_ = l_Lean_Name_mkStr2(v___x_9_, v___x_63_);
v___x_65_ = l_Lean_mkConst(v___x_64_, v___x_24_);
lean_inc_ref(v___x_65_);
v___x_66_ = l_Lean_mkApp3(v___x_65_, v_a_15_, v_a_17_, v_p_25_);
v___x_67_ = l_Lean_mkApp3(v___x_65_, v_a_15_, v_a_17_, v_q_26_);
v___x_68_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4));
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
v___x_80_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5));
lean_inc_ref(v___x_32_);
v___x_81_ = l_Lean_Name_mkStr2(v___x_32_, v___x_80_);
v___x_82_ = l_Lean_mkConst(v___x_81_, v___x_11_);
v___x_83_ = l_Lean_mkAppB(v___x_82_, v_prop_20_, v_a_73_);
v___x_84_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed(lean_object** _args){
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
uint8_t v___x_2438__boxed_126_; uint8_t v___x_2439__boxed_127_; uint8_t v___x_2440__boxed_128_; lean_object* v_res_129_; 
v___x_2438__boxed_126_ = lean_unbox(v___x_107_);
v___x_2439__boxed_127_ = lean_unbox(v___x_108_);
v___x_2440__boxed_128_ = lean_unbox(v___x_109_);
v_res_129_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(v___x_95_, v_a_96_, v___x_97_, v___x_98_, v_xs_99_, v___x_100_, v_a_101_, v___x_102_, v_a_103_, v___x_104_, v___x_105_, v_prop_106_, v___x_2438__boxed_126_, v___x_2439__boxed_127_, v___x_2440__boxed_128_, v___x_110_, v_p_111_, v_q_112_, v_h_113_, v___x_114_, v___x_115_, v___x_116_, v___x_117_, v___x_118_, v___x_119_, v_p_x27_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec_ref(v_xs_99_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(lean_object* v_k_130_, lean_object* v_b_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_138_, lean_object* v_b_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(v_k_138_, v_b_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(lean_object* v_name_146_, uint8_t v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, uint8_t v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_156_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___boxed(lean_object* v_name_174_, lean_object* v_bi_175_, lean_object* v_type_176_, lean_object* v_k_177_, lean_object* v_kind_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_bi_boxed_184_; uint8_t v_kind_boxed_185_; lean_object* v_res_186_; 
v_bi_boxed_184_ = lean_unbox(v_bi_175_);
v_kind_boxed_185_ = lean_unbox(v_kind_178_);
v_res_186_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_174_, v_bi_boxed_184_, v_type_176_, v_k_177_, v_kind_boxed_185_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(lean_object* v_name_187_, lean_object* v_type_188_, lean_object* v_k_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = 0;
v___x_196_ = 0;
v___x_197_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_187_, v___x_195_, v_type_188_, v_k_189_, v___x_196_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg___boxed(lean_object* v_name_198_, lean_object* v_type_199_, lean_object* v_k_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_198_, v_type_199_, v_k_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(lean_object* v_xs_213_, lean_object* v___x_214_, uint8_t v___x_215_, uint8_t v___x_216_, uint8_t v___x_217_, lean_object* v_p_218_, lean_object* v_q_219_, lean_object* v_a_220_, lean_object* v___x_221_, lean_object* v_a_222_, lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v_prop_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v___x_234_, lean_object* v_h_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
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
v___x_249_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0));
v___x_250_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1));
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
v___f_257_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed), 31, 25);
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
lean_closure_set(v___f_257_, 19, v___x_253_);
lean_closure_set(v___f_257_, 20, v___x_230_);
lean_closure_set(v___f_257_, 21, v___x_231_);
lean_closure_set(v___f_257_, 22, v___x_232_);
lean_closure_set(v___f_257_, 23, v___x_233_);
lean_closure_set(v___f_257_, 24, v___x_234_);
v___x_258_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3));
v___x_259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_258_, v___x_253_, v___f_257_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed(lean_object** _args){
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
uint8_t v___x_2727__boxed_288_; uint8_t v___x_2728__boxed_289_; uint8_t v___x_2729__boxed_290_; lean_object* v_res_291_; 
v___x_2727__boxed_288_ = lean_unbox(v___x_262_);
v___x_2728__boxed_289_ = lean_unbox(v___x_263_);
v___x_2729__boxed_290_ = lean_unbox(v___x_264_);
v_res_291_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(v_xs_260_, v___x_261_, v___x_2727__boxed_288_, v___x_2728__boxed_289_, v___x_2729__boxed_290_, v_p_265_, v_q_266_, v_a_267_, v___x_268_, v_a_269_, v___x_270_, v___x_271_, v___x_272_, v___x_273_, v___x_274_, v___x_275_, v_prop_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, v___x_281_, v_h_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = l_Lean_Level_ofNat(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_301_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1));
v___x_302_ = l_Lean_mkConst(v___x_301_, v___x_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(lean_object* v_p_306_, lean_object* v_xs_307_, lean_object* v_prop_308_, uint8_t v___x_309_, uint8_t v___x_310_, uint8_t v___x_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v___x_314_, lean_object* v___x_315_, lean_object* v___x_316_, lean_object* v___x_317_, lean_object* v_q_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_324_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0));
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_box(0);
v___x_327_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_328_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4);
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
v___x_334_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6));
v___x_335_ = lean_box(v___x_309_);
v___x_336_ = lean_box(v___x_310_);
v___x_337_ = lean_box(v___x_311_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed), 28, 22);
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
v___x_339_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_334_, v_a_333_, v___f_338_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed(lean_object** _args){
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
uint8_t v___x_2869__boxed_358_; uint8_t v___x_2870__boxed_359_; uint8_t v___x_2871__boxed_360_; lean_object* v_res_361_; 
v___x_2869__boxed_358_ = lean_unbox(v___x_343_);
v___x_2870__boxed_359_ = lean_unbox(v___x_344_);
v___x_2871__boxed_360_ = lean_unbox(v___x_345_);
v_res_361_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(v_p_340_, v_xs_341_, v_prop_342_, v___x_2869__boxed_358_, v___x_2870__boxed_359_, v___x_2871__boxed_360_, v_a_346_, v_a_347_, v___x_348_, v___x_349_, v___x_350_, v___x_351_, v_q_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(lean_object* v_xs_365_, lean_object* v_prop_366_, uint8_t v___x_367_, uint8_t v___x_368_, uint8_t v___x_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v___x_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v_p_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; 
v___x_381_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1));
v___x_382_ = lean_box(v___x_367_);
v___x_383_ = lean_box(v___x_368_);
v___x_384_ = lean_box(v___x_369_);
lean_inc_ref(v_a_371_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed), 18, 12);
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
v___x_386_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_381_, v_a_371_, v___f_385_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed(lean_object* v_xs_387_, lean_object* v_prop_388_, lean_object* v___x_389_, lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_p_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v___x_2964__boxed_403_; uint8_t v___x_2965__boxed_404_; uint8_t v___x_2966__boxed_405_; lean_object* v_res_406_; 
v___x_2964__boxed_403_ = lean_unbox(v___x_389_);
v___x_2965__boxed_404_ = lean_unbox(v___x_390_);
v___x_2966__boxed_405_ = lean_unbox(v___x_391_);
v_res_406_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(v_xs_387_, v_prop_388_, v___x_2964__boxed_403_, v___x_2965__boxed_404_, v___x_2966__boxed_405_, v_a_392_, v_a_393_, v___x_394_, v___x_395_, v___x_396_, v_p_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_406_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = l_Lean_Level_ofNat(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1(void){
_start:
{
lean_object* v___x_409_; lean_object* v_prop_410_; 
v___x_409_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v_prop_410_ = l_Lean_mkSort(v___x_409_);
return v_prop_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor(lean_object* v_xs_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_prop_422_; uint8_t v___x_423_; uint8_t v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v_prop_422_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1);
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
v___x_430_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3));
v___x_431_ = lean_box(v___x_423_);
v___x_432_ = lean_box(v___x_424_);
v___x_433_ = lean_box(v___x_425_);
lean_inc(v_a_427_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed), 16, 10);
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
v___x_435_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_430_, v_a_427_, v___f_434_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor___boxed(lean_object* v_xs_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(lean_object* v_00_u03b1_451_, lean_object* v_name_452_, uint8_t v_bi_453_, lean_object* v_type_454_, lean_object* v_k_455_, uint8_t v_kind_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_452_, v_bi_453_, v_type_454_, v_k_455_, v_kind_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_463_, lean_object* v_name_464_, lean_object* v_bi_465_, lean_object* v_type_466_, lean_object* v_k_467_, lean_object* v_kind_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v_bi_boxed_474_; uint8_t v_kind_boxed_475_; lean_object* v_res_476_; 
v_bi_boxed_474_ = lean_unbox(v_bi_465_);
v_kind_boxed_475_ = lean_unbox(v_kind_468_);
v_res_476_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(v_00_u03b1_463_, v_name_464_, v_bi_boxed_474_, v_type_466_, v_k_467_, v_kind_boxed_475_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(lean_object* v_00_u03b1_477_, lean_object* v_name_478_, lean_object* v_type_479_, lean_object* v_k_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_478_, v_type_479_, v_k_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___boxed(lean_object* v_00_u03b1_487_, lean_object* v_name_488_, lean_object* v_type_489_, lean_object* v_k_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(v_00_u03b1_487_, v_name_488_, v_type_489_, v_k_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
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
v_debug_542_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*12);
lean_dec(v___x_541_);
if (v_debug_542_ == 0)
{
v___y_538_ = v___y_531_;
goto v___jp_537_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; 
lean_dec_ref_known(v___x_543_, 1);
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
lean_dec_ref_known(v_e_600_, 3);
v___x_638_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(v_body_635_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_arrow_640_; lean_object* v_infos_641_; lean_object* v_v_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_693_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
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
lean_dec_ref_known(v___x_646_, 1);
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
lean_dec_ref_known(v___x_652_, 1);
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
v_debug_719_ = lean_ctor_get_uint8(v___x_718_, sizeof(void*)*12);
lean_dec(v___x_718_);
if (v_debug_719_ == 0)
{
v___y_715_ = v___y_708_;
goto v___jp_714_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_721_; 
lean_dec_ref_known(v___x_720_, 1);
v___x_721_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_dec_ref_known(v___x_721_, 1);
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
lean_dec_ref_known(v_infos_752_, 2);
v_binderName_762_ = lean_ctor_get(v_head_760_, 0);
lean_inc(v_binderName_762_);
v_binderInfo_763_ = lean_ctor_get_uint8(v_head_760_, sizeof(void*)*3);
lean_dec(v_head_760_);
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
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_764_);
v___x_768_ = l_Lean_Expr_isApp(v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_767_);
lean_dec_ref(v___x_764_);
lean_dec(v_binderName_762_);
lean_dec(v_tail_761_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_e_751_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_767_);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_772_ = l_Lean_Expr_isConstOf(v___x_770_, v___x_771_);
lean_dec_ref(v___x_770_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v___x_767_);
lean_dec_ref(v___x_764_);
lean_dec(v_binderName_762_);
lean_dec(v_tail_761_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_e_751_);
return v___x_773_;
}
else
{
lean_object* v_arg_774_; lean_object* v_arg_775_; lean_object* v___x_776_; 
lean_dec_ref(v_e_751_);
v_arg_774_ = lean_ctor_get(v___x_764_, 1);
lean_inc_ref(v_arg_774_);
lean_dec_ref(v___x_764_);
v_arg_775_ = lean_ctor_get(v___x_767_, 1);
lean_inc_ref(v_arg_775_);
lean_dec_ref(v___x_767_);
v___x_776_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(v_arg_774_, v_tail_761_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_binderName_762_, v_binderInfo_763_, v_arg_775_, v_a_777_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
return v___x_778_;
}
else
{
lean_dec_ref(v_arg_775_);
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
v_debug_812_ = lean_ctor_get_uint8(v___x_811_, sizeof(void*)*12);
lean_dec(v___x_811_);
if (v_debug_812_ == 0)
{
v___y_808_ = v___y_801_;
goto v___jp_807_;
}
else
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_798_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_814_; 
lean_dec_ref_known(v___x_813_, 1);
v___x_814_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref_known(v___x_814_, 1);
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
lean_dec_ref_known(v___x_854_, 1);
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
lean_object* v___y_947_; lean_object* v___y_948_; uint8_t v___y_949_; lean_object* v___y_950_; uint8_t v___y_951_; uint8_t v___y_956_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; 
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
v___x_1018_ = l_Lean_Expr_cleanupAnnotations(v_e_933_);
v___x_1019_ = l_Lean_Expr_isApp(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec_ref(v___x_1018_);
v___y_961_ = v_a_936_;
v___y_962_ = v_a_937_;
v___y_963_ = v_a_938_;
v___y_964_ = v_a_939_;
v___y_965_ = v_a_940_;
v___y_966_ = v_a_941_;
v___y_967_ = v_a_942_;
v___y_968_ = v_a_943_;
v___y_969_ = v_a_944_;
goto v___jp_960_;
}
else
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1018_);
v___x_1021_ = l_Lean_Expr_isApp(v___x_1020_);
if (v___x_1021_ == 0)
{
lean_dec_ref(v___x_1020_);
lean_dec_ref(v___x_1018_);
v___y_961_ = v_a_936_;
v___y_962_ = v_a_937_;
v___y_963_ = v_a_938_;
v___y_964_ = v_a_939_;
v___y_965_ = v_a_940_;
v___y_966_ = v_a_941_;
v___y_967_ = v_a_942_;
v___y_968_ = v_a_943_;
v___y_969_ = v_a_944_;
goto v___jp_960_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1020_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2));
v___x_1024_ = l_Lean_Expr_isConstOf(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec_ref(v___x_1022_);
lean_dec_ref(v___x_1020_);
lean_dec_ref(v___x_1018_);
v___y_961_ = v_a_936_;
v___y_962_ = v_a_937_;
v___y_963_ = v_a_938_;
v___y_964_ = v_a_939_;
v___y_965_ = v_a_940_;
v___y_966_ = v_a_941_;
v___y_967_ = v_a_942_;
v___y_968_ = v_a_943_;
v___y_969_ = v_a_944_;
goto v___jp_960_;
}
else
{
lean_object* v_arg_1025_; lean_object* v_arg_1026_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; lean_object* v___y_1051_; uint8_t v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1055_; uint8_t v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v_proof_1111_; uint8_t v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; uint8_t v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1214_; lean_object* v___y_1215_; uint8_t v___y_1216_; lean_object* v___y_1243_; lean_object* v___y_1244_; uint8_t v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___x_1273_; 
lean_dec_ref(v_e_933_);
v_arg_1025_ = lean_ctor_get(v___x_1018_, 1);
lean_inc_ref(v_arg_1025_);
lean_dec_ref(v___x_1018_);
v_arg_1026_ = lean_ctor_get(v___x_1020_, 1);
lean_inc_ref_n(v_arg_1026_, 2);
lean_dec_ref(v___x_1020_);
lean_inc(v_a_944_);
lean_inc_ref(v_a_943_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
v___x_1273_ = lean_sym_simp(v_arg_1026_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1026_, v_a_1274_);
v___x_1276_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v___x_1275_, v_a_939_);
lean_dec_ref(v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; uint8_t v___y_1279_; uint8_t v___x_1342_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1342_ = lean_unbox(v_a_1277_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_unbox(v_a_1277_);
lean_dec(v_a_1277_);
v___y_1279_ = v___x_1343_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_dec(v_a_1277_);
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
lean_dec_ref(v___x_1022_);
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
if (lean_obj_tag(v_a_1274_) == 0)
{
uint8_t v_contextDependent_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_arg_1026_);
v_contextDependent_1349_ = lean_ctor_get_uint8(v_a_1274_, 1);
lean_dec_ref_known(v_a_1274_, 0);
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
v___x_1357_ = l_Lean_Expr_app___override(v___x_1356_, v_arg_1025_);
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
lean_dec_ref(v_arg_1025_);
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
v_proof_1375_ = lean_ctor_get(v_a_1274_, 1);
v_contextDependent_1376_ = lean_ctor_get_uint8(v_a_1274_, sizeof(void*)*2 + 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1274_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_a_1274_, 0);
lean_dec(v_unused_1408_);
v___x_1378_ = v_a_1274_;
v_isShared_1379_ = v_isSharedCheck_1407_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_proof_1375_);
lean_dec(v_a_1274_);
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
v___x_1387_ = l_Lean_mkApp3(v___x_1386_, v_arg_1026_, v_arg_1025_, v_proof_1375_);
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
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
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
v___jp_1278_:
{
lean_object* v___x_1280_; 
lean_inc(v_tail_1007_);
lean_inc_ref(v_arg_1025_);
v___x_1280_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(v_arg_1025_, v_tail_1007_, v_simpBody_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v_fst_1282_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_fst_1282_);
v_snd_1283_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_snd_1283_);
lean_dec(v_a_1281_);
v___x_1284_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_1025_, v_fst_1282_);
v___x_1285_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___x_1284_, v_a_939_);
lean_dec_ref(v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; uint8_t v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = lean_unbox(v_a_1286_);
if (v___x_1287_ == 0)
{
if (lean_obj_tag(v_a_1274_) == 0)
{
if (lean_obj_tag(v_fst_1282_) == 0)
{
uint8_t v_contextDependent_1288_; 
lean_dec_ref(v___x_1022_);
v_contextDependent_1288_ = lean_ctor_get_uint8(v_a_1274_, 1);
lean_dec_ref_known(v_a_1274_, 0);
if (v_contextDependent_1288_ == 0)
{
uint8_t v_contextDependent_1289_; uint8_t v___x_1290_; 
v_contextDependent_1289_ = lean_ctor_get_uint8(v_fst_1282_, 1);
lean_dec_ref_known(v_fst_1282_, 0);
v___x_1290_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1176_ = v___x_1290_;
v___y_1177_ = v_snd_1283_;
v___y_1178_ = v_contextDependent_1289_;
goto v___jp_1175_;
}
else
{
uint8_t v___x_1291_; 
lean_dec_ref_known(v_fst_1282_, 0);
v___x_1291_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1176_ = v___x_1291_;
v___y_1177_ = v_snd_1283_;
v___y_1178_ = v___x_1024_;
goto v___jp_1175_;
}
}
else
{
uint8_t v_contextDependent_1292_; 
lean_inc(v_head_1006_);
lean_dec_ref_known(v_infos_934_, 2);
v_contextDependent_1292_ = lean_ctor_get_uint8(v_a_1274_, 1);
lean_dec_ref_known(v_a_1274_, 0);
if (v_contextDependent_1292_ == 0)
{
lean_object* v_e_x27_1293_; lean_object* v_proof_1294_; uint8_t v_contextDependent_1295_; uint8_t v___x_1296_; 
v_e_x27_1293_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc_ref(v_e_x27_1293_);
v_proof_1294_ = lean_ctor_get(v_fst_1282_, 1);
lean_inc_ref(v_proof_1294_);
v_contextDependent_1295_ = lean_ctor_get_uint8(v_fst_1282_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1282_, 2);
v___x_1296_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1212_ = v_proof_1294_;
v___y_1213_ = v_e_x27_1293_;
v___y_1214_ = v___x_1296_;
v___y_1215_ = v_snd_1283_;
v___y_1216_ = v_contextDependent_1295_;
goto v___jp_1211_;
}
else
{
lean_object* v_e_x27_1297_; lean_object* v_proof_1298_; uint8_t v___x_1299_; 
v_e_x27_1297_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc_ref(v_e_x27_1297_);
v_proof_1298_ = lean_ctor_get(v_fst_1282_, 1);
lean_inc_ref(v_proof_1298_);
lean_dec_ref_known(v_fst_1282_, 2);
v___x_1299_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1212_ = v_proof_1298_;
v___y_1213_ = v_e_x27_1297_;
v___y_1214_ = v___x_1299_;
v___y_1215_ = v_snd_1283_;
v___y_1216_ = v___x_1024_;
goto v___jp_1211_;
}
}
}
else
{
lean_inc(v_head_1006_);
lean_dec_ref_known(v_infos_934_, 2);
if (lean_obj_tag(v_fst_1282_) == 0)
{
uint8_t v_contextDependent_1300_; 
v_contextDependent_1300_ = lean_ctor_get_uint8(v_a_1274_, sizeof(void*)*2 + 1);
if (v_contextDependent_1300_ == 0)
{
lean_object* v_e_x27_1301_; lean_object* v_proof_1302_; uint8_t v_contextDependent_1303_; uint8_t v___x_1304_; 
v_e_x27_1301_ = lean_ctor_get(v_a_1274_, 0);
lean_inc_ref(v_e_x27_1301_);
v_proof_1302_ = lean_ctor_get(v_a_1274_, 1);
lean_inc_ref(v_proof_1302_);
lean_dec_ref_known(v_a_1274_, 2);
v_contextDependent_1303_ = lean_ctor_get_uint8(v_fst_1282_, 1);
lean_dec_ref_known(v_fst_1282_, 0);
v___x_1304_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1243_ = v_e_x27_1301_;
v___y_1244_ = v_proof_1302_;
v___y_1245_ = v___x_1304_;
v___y_1246_ = v_snd_1283_;
v___y_1247_ = v_contextDependent_1303_;
goto v___jp_1242_;
}
else
{
lean_object* v_e_x27_1305_; lean_object* v_proof_1306_; uint8_t v___x_1307_; 
lean_dec_ref_known(v_fst_1282_, 0);
v_e_x27_1305_ = lean_ctor_get(v_a_1274_, 0);
lean_inc_ref(v_e_x27_1305_);
v_proof_1306_ = lean_ctor_get(v_a_1274_, 1);
lean_inc_ref(v_proof_1306_);
lean_dec_ref_known(v_a_1274_, 2);
v___x_1307_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_1243_ = v_e_x27_1305_;
v___y_1244_ = v_proof_1306_;
v___y_1245_ = v___x_1307_;
v___y_1246_ = v_snd_1283_;
v___y_1247_ = v___x_1024_;
goto v___jp_1242_;
}
}
else
{
lean_object* v_e_x27_1308_; lean_object* v_proof_1309_; uint8_t v_contextDependent_1310_; lean_object* v_e_x27_1311_; lean_object* v_proof_1312_; uint8_t v_contextDependent_1313_; lean_object* v___x_1314_; 
v_e_x27_1308_ = lean_ctor_get(v_a_1274_, 0);
lean_inc_ref(v_e_x27_1308_);
v_proof_1309_ = lean_ctor_get(v_a_1274_, 1);
lean_inc_ref(v_proof_1309_);
v_contextDependent_1310_ = lean_ctor_get_uint8(v_a_1274_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1274_, 2);
v_e_x27_1311_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc_ref(v_e_x27_1311_);
v_proof_1312_ = lean_ctor_get(v_fst_1282_, 1);
lean_inc_ref(v_proof_1312_);
v_contextDependent_1313_ = lean_ctor_get_uint8(v_fst_1282_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1282_, 2);
v___x_1314_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1308_, v_a_939_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = lean_unbox(v_a_1315_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; 
lean_dec(v_a_1286_);
v___x_1317_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
v___y_1028_ = v_e_x27_1308_;
v___y_1029_ = v_e_x27_1311_;
v___y_1030_ = v_proof_1312_;
v___y_1031_ = v_contextDependent_1310_;
v___y_1032_ = v_contextDependent_1313_;
v___y_1033_ = v_proof_1309_;
v___y_1034_ = v_snd_1283_;
v___y_1035_ = v___x_1317_;
goto v___jp_1027_;
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
v___y_1028_ = v_e_x27_1308_;
v___y_1029_ = v_e_x27_1311_;
v___y_1030_ = v_proof_1312_;
v___y_1031_ = v_contextDependent_1310_;
v___y_1032_ = v_contextDependent_1313_;
v___y_1033_ = v_proof_1309_;
v___y_1034_ = v_snd_1283_;
v___y_1035_ = v___x_1319_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_e_x27_1308_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21);
lean_inc_ref(v_e_x27_1311_);
v___x_1321_ = l_Lean_mkApp5(v___x_1320_, v_arg_1026_, v_arg_1025_, v_e_x27_1311_, v_proof_1309_, v_proof_1312_);
if (v_contextDependent_1310_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_947_ = v_e_x27_1311_;
v___y_948_ = v___x_1321_;
v___y_949_ = v___x_1322_;
v___y_950_ = v_snd_1283_;
v___y_951_ = v_contextDependent_1313_;
goto v___jp_946_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
v___y_947_ = v_e_x27_1311_;
v___y_948_ = v___x_1321_;
v___y_949_ = v___x_1323_;
v___y_950_ = v_snd_1283_;
v___y_951_ = v___x_1024_;
goto v___jp_946_;
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
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
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
lean_dec_ref(v___x_1022_);
lean_dec_ref_known(v_infos_934_, 2);
if (lean_obj_tag(v_a_1274_) == 0)
{
uint8_t v_contextDependent_1332_; 
v_contextDependent_1332_ = lean_ctor_get_uint8(v_a_1274_, 1);
lean_dec_ref_known(v_a_1274_, 0);
v___y_1168_ = v_fst_1282_;
v___y_1169_ = v___y_1279_;
v___y_1170_ = v_contextDependent_1332_;
goto v___jp_1167_;
}
else
{
uint8_t v_contextDependent_1333_; 
v_contextDependent_1333_ = lean_ctor_get_uint8(v_a_1274_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1274_, 2);
v___y_1168_ = v_fst_1282_;
v___y_1169_ = v___y_1279_;
v___y_1170_ = v_contextDependent_1333_;
goto v___jp_1167_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_snd_1283_);
lean_dec(v_fst_1282_);
lean_dec(v_a_1274_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec_ref_known(v_infos_934_, 2);
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
lean_dec(v_a_1274_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec_ref_known(v_infos_934_, 2);
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_a_1274_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec_ref_known(v_infos_934_, 2);
lean_dec_ref(v_simpBody_935_);
v_a_1412_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1276_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1276_);
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
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec_ref_known(v_infos_934_, 2);
lean_dec_ref(v_simpBody_935_);
v_a_1420_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1273_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1273_);
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
v___jp_1027_:
{
lean_object* v___x_1036_; 
lean_inc_ref(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc_ref(v___x_1022_);
v___x_1036_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1022_, v___y_1028_, v___y_1029_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1));
v___x_1039_ = l_Lean_Expr_constLevels_x21(v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1040_ = l_Lean_mkConst(v___x_1038_, v___x_1039_);
v___x_1041_ = l_Lean_mkApp6(v___x_1040_, v_arg_1026_, v___y_1028_, v_arg_1025_, v___y_1029_, v___y_1033_, v___y_1030_);
if (v___y_1031_ == 0)
{
v___y_1009_ = v___y_1035_;
v___y_1010_ = v___x_1041_;
v___y_1011_ = v___y_1034_;
v___y_1012_ = v_a_1037_;
v___y_1013_ = v___y_1032_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v___y_1035_;
v___y_1010_ = v___x_1041_;
v___y_1011_ = v___y_1034_;
v___y_1012_ = v_a_1037_;
v___y_1013_ = v___x_1024_;
goto v___jp_1008_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v_a_1042_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1036_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1036_);
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
v___jp_1050_:
{
lean_object* v___x_1056_; 
lean_inc_ref(v_arg_1025_);
lean_inc_ref(v___y_1051_);
lean_inc_ref(v___x_1022_);
v___x_1056_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1022_, v___y_1051_, v_arg_1025_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1071_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1071_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1071_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3));
v___x_1062_ = l_Lean_Expr_constLevels_x21(v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1063_ = l_Lean_mkConst(v___x_1061_, v___x_1062_);
v___x_1064_ = l_Lean_mkApp4(v___x_1063_, v_arg_1026_, v___y_1051_, v_arg_1025_, v___y_1053_);
v___x_1065_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1065_, 0, v_a_1057_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*2, v___y_1055_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*2 + 1, v___y_1052_);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_head_1006_);
lean_ctor_set(v___x_1066_, 1, v___y_1054_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1067_);
v___x_1069_ = v___x_1059_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v_a_1072_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1056_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1056_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
v___jp_1080_:
{
lean_object* v___x_1086_; 
lean_inc_ref(v___y_1083_);
lean_inc_ref(v_arg_1026_);
lean_inc_ref(v___x_1022_);
v___x_1086_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_1022_, v_arg_1026_, v___y_1083_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1101_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1101_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1101_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5));
v___x_1092_ = l_Lean_Expr_constLevels_x21(v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1093_ = l_Lean_mkConst(v___x_1091_, v___x_1092_);
v___x_1094_ = l_Lean_mkApp4(v___x_1093_, v_arg_1026_, v_arg_1025_, v___y_1083_, v___y_1082_);
v___x_1095_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1095_, 0, v_a_1087_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2, v___y_1085_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2 + 1, v___y_1081_);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_head_1006_);
lean_ctor_set(v___x_1096_, 1, v___y_1084_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1097_);
v___x_1099_ = v___x_1089_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v_a_1102_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1086_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1086_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
v___jp_1110_:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_939_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1130_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1130_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1130_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_u_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v_u_1119_ = lean_ctor_get(v_head_1006_, 1);
lean_inc(v_u_1119_);
lean_dec(v_head_1006_);
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7));
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_u_1119_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_mkConst(v___x_1120_, v___x_1122_);
v___x_1124_ = l_Lean_mkApp3(v___x_1123_, v_arg_1026_, v_arg_1025_, v_proof_1111_);
v___x_1125_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1125_, 0, v_a_1115_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*2, v___y_1112_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*2 + 1, v___y_1113_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1121_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1126_);
v___x_1128_ = v___x_1117_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_proof_1111_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec(v_head_1006_);
v_a_1131_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1114_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1114_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
v___jp_1139_:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_939_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1158_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_u_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v_u_1147_ = lean_ctor_get(v_head_1006_, 1);
lean_inc(v_u_1147_);
lean_dec(v_head_1006_);
v___x_1148_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9));
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_u_1147_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_mkConst(v___x_1148_, v___x_1150_);
v___x_1152_ = l_Lean_Expr_app___override(v___x_1151_, v_arg_1026_);
v___x_1153_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1153_, 0, v_a_1143_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*2, v___y_1140_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*2 + 1, v___y_1141_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1149_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1154_);
v___x_1156_ = v___x_1145_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_arg_1026_);
lean_dec(v_head_1006_);
v_a_1159_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1142_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1142_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
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
v___jp_1167_:
{
if (v___y_1170_ == 0)
{
if (lean_obj_tag(v___y_1168_) == 0)
{
uint8_t v_contextDependent_1171_; 
lean_dec_ref(v_arg_1025_);
v_contextDependent_1171_ = lean_ctor_get_uint8(v___y_1168_, 1);
lean_dec_ref_known(v___y_1168_, 0);
v___y_1140_ = v___y_1169_;
v___y_1141_ = v_contextDependent_1171_;
goto v___jp_1139_;
}
else
{
lean_object* v_proof_1172_; uint8_t v_contextDependent_1173_; 
v_proof_1172_ = lean_ctor_get(v___y_1168_, 1);
lean_inc_ref(v_proof_1172_);
v_contextDependent_1173_ = lean_ctor_get_uint8(v___y_1168_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_1168_, 2);
v_proof_1111_ = v_proof_1172_;
v___y_1112_ = v___y_1169_;
v___y_1113_ = v_contextDependent_1173_;
goto v___jp_1110_;
}
}
else
{
if (lean_obj_tag(v___y_1168_) == 0)
{
lean_dec_ref_known(v___y_1168_, 0);
lean_dec_ref(v_arg_1025_);
v___y_1140_ = v___y_1169_;
v___y_1141_ = v___x_1024_;
goto v___jp_1139_;
}
else
{
lean_object* v_proof_1174_; 
v_proof_1174_ = lean_ctor_get(v___y_1168_, 1);
lean_inc_ref(v_proof_1174_);
lean_dec_ref_known(v___y_1168_, 2);
v_proof_1111_ = v_proof_1174_;
v___y_1112_ = v___y_1169_;
v___y_1113_ = v___x_1024_;
goto v___jp_1110_;
}
}
}
v___jp_1175_:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1026_, v_a_939_);
lean_dec_ref(v_arg_1026_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1202_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1202_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1202_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_unbox(v_a_1180_);
lean_dec(v_a_1180_);
if (v___x_1184_ == 0)
{
lean_del_object(v___x_1182_);
lean_dec(v___y_1177_);
lean_dec_ref(v_arg_1025_);
v___y_956_ = v___y_1178_;
goto v___jp_955_;
}
else
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_del_object(v___x_1182_);
lean_dec(v___y_1177_);
lean_dec_ref(v_arg_1025_);
v___y_956_ = v___y_1178_;
goto v___jp_955_;
}
else
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1199_; 
v_isSharedCheck_1199_ = !lean_is_exclusive(v_infos_934_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1200_ = lean_ctor_get(v_infos_934_, 1);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_infos_934_, 0);
lean_dec(v_unused_1201_);
v___x_1188_ = v_infos_934_;
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_infos_934_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12);
lean_inc_ref(v_arg_1025_);
v___x_1191_ = l_Lean_Expr_app___override(v___x_1190_, v_arg_1025_);
v___x_1192_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1192_, 0, v_arg_1025_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
lean_ctor_set_uint8(v___x_1192_, sizeof(void*)*2, v___y_1176_);
lean_ctor_set_uint8(v___x_1192_, sizeof(void*)*2 + 1, v___y_1178_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 0);
lean_ctor_set(v___x_1188_, 1, v___y_1177_);
lean_ctor_set(v___x_1188_, 0, v___x_1192_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___y_1177_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1194_);
v___x_1196_ = v___x_1182_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v___y_1177_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref_known(v_infos_934_, 2);
v_a_1203_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1179_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1179_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
v___jp_1211_:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1026_, v_a_939_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1233_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1233_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1233_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_unbox(v_a_1218_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; 
lean_del_object(v___x_1220_);
v___x_1223_ = lean_unbox(v_a_1218_);
lean_dec(v_a_1218_);
v___y_1081_ = v___y_1216_;
v___y_1082_ = v___y_1212_;
v___y_1083_ = v___y_1213_;
v___y_1084_ = v___y_1215_;
v___y_1085_ = v___x_1223_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
lean_dec(v_a_1218_);
v___x_1224_ = lean_box(0);
v___x_1225_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_del_object(v___x_1220_);
v___y_1081_ = v___y_1216_;
v___y_1082_ = v___y_1212_;
v___y_1083_ = v___y_1213_;
v___y_1084_ = v___y_1215_;
v___y_1085_ = v___x_1225_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v___x_1226_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15);
lean_inc_ref(v___y_1213_);
v___x_1227_ = l_Lean_mkApp3(v___x_1226_, v_arg_1025_, v___y_1213_, v___y_1212_);
v___x_1228_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1228_, 0, v___y_1213_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*2, v___y_1214_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*2 + 1, v___y_1216_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___y_1215_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1229_);
v___x_1231_ = v___x_1220_;
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
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v_a_1234_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1217_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1217_);
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
v___jp_1242_:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___y_1243_, v_a_939_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1264_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1264_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1264_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_unbox(v_a_1249_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
lean_del_object(v___x_1251_);
v___x_1254_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
v___y_1051_ = v___y_1243_;
v___y_1052_ = v___y_1247_;
v___y_1053_ = v___y_1244_;
v___y_1054_ = v___y_1246_;
v___y_1055_ = v___x_1254_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
lean_dec(v_a_1249_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_1006_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_del_object(v___x_1251_);
v___y_1051_ = v___y_1243_;
v___y_1052_ = v___y_1247_;
v___y_1053_ = v___y_1244_;
v___y_1054_ = v___y_1246_;
v___y_1055_ = v___x_1256_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_dec_ref(v___y_1243_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v___x_1257_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18);
lean_inc_ref(v_arg_1025_);
v___x_1258_ = l_Lean_mkApp3(v___x_1257_, v_arg_1026_, v_arg_1025_, v___y_1244_);
v___x_1259_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1259_, 0, v_arg_1025_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*2, v___y_1245_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*2 + 1, v___y_1247_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___y_1246_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1260_);
v___x_1262_ = v___x_1251_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
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
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_arg_1025_);
lean_dec_ref(v___x_1022_);
lean_dec(v_head_1006_);
v_a_1265_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1248_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1248_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
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
lean_ctor_set(v___x_1014_, 1, v___y_1010_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*2, v___y_1009_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*2 + 1, v___y_1013_);
v___x_1015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_head_1006_);
lean_ctor_set(v___x_1015_, 1, v___y_1011_);
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
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_952_, 0, v___y_947_);
lean_ctor_set(v___x_952_, 1, v___y_948_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*2, v___y_949_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*2 + 1, v___y_951_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v___y_950_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_infos_934_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
v___jp_960_:
{
lean_object* v___x_970_; 
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
v___x_970_ = lean_apply_11(v_simpBody_935_, v_e_933_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_979_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_a_971_);
lean_ctor_set(v___x_975_, 1, v_infos_934_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_infos_934_);
v_a_980_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_970_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_970_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
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
lean_dec_ref_known(v___x_1490_, 1);
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
lean_dec_ref_known(v_fst_1500_, 0);
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
v_debug_1599_ = lean_ctor_get_uint8(v___x_1598_, sizeof(void*)*12);
lean_dec(v___x_1598_);
if (v_debug_1599_ == 0)
{
v___y_1595_ = v___y_1588_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1585_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref_known(v___x_1600_, 1);
v___x_1601_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
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
v___x_1662_ = l_instMonadEIO___redArg();
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
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_24914__overap_1734_; lean_object* v___x_1735_; 
v___x_1727_ = l_StateRefT_x27_instMonad___redArg(v___x_1726_);
v___x_1728_ = l_ReaderT_instMonad___redArg(v___x_1727_);
v___x_1729_ = l_StateRefT_x27_instMonad___redArg(v___x_1728_);
v___x_1730_ = l_ReaderT_instMonad___redArg(v___x_1729_);
v___x_1731_ = l_ReaderT_instMonad___redArg(v___x_1730_);
v___x_1732_ = l_Lean_instInhabitedExpr;
v___x_1733_ = l_instInhabitedOfMonad___redArg(v___x_1731_, v___x_1732_);
v___x_24914__overap_1734_ = lean_panic_fn_borrowed(v___x_1733_, v_msg_1667_);
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
v___x_1735_ = lean_apply_10(v___x_24914__overap_1734_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, lean_box(0));
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
lean_object* v___y_1790_; uint8_t v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1804_; uint8_t v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v_p_1810_; lean_object* v_q_1811_; lean_object* v___x_1812_; 
v_p_1810_ = l_Lean_Expr_bindingDomain_x21(v_e_1778_);
v_q_1811_ = l_Lean_Expr_bindingBody_x21(v_e_1778_);
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
v___x_1812_ = lean_sym_simp(v_p_1810_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
lean_inc(v_a_1787_);
lean_inc_ref(v_a_1786_);
lean_inc(v_a_1785_);
lean_inc_ref(v_a_1784_);
lean_inc(v_a_1783_);
lean_inc_ref(v_a_1782_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_q_1811_);
v___x_1814_ = lean_sym_simp(v_q_1811_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_2003_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_2003_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_2003_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
uint8_t v___y_1820_; 
if (lean_obj_tag(v_a_1813_) == 0)
{
if (lean_obj_tag(v_a_1815_) == 0)
{
uint8_t v_contextDependent_1825_; 
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_contextDependent_1825_ = lean_ctor_get_uint8(v_a_1813_, 1);
lean_dec_ref_known(v_a_1813_, 0);
if (v_contextDependent_1825_ == 0)
{
uint8_t v_contextDependent_1826_; 
v_contextDependent_1826_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref_known(v_a_1815_, 0);
v___y_1820_ = v_contextDependent_1826_;
goto v___jp_1819_;
}
else
{
lean_dec_ref_known(v_a_1815_, 0);
v___y_1820_ = v_contextDependent_1825_;
goto v___jp_1819_;
}
}
else
{
uint8_t v_contextDependent_1827_; lean_object* v_e_x27_1828_; lean_object* v_proof_1829_; uint8_t v_contextDependent_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1817_);
v_contextDependent_1827_ = lean_ctor_get_uint8(v_a_1813_, 1);
lean_dec_ref_known(v_a_1813_, 0);
v_e_x27_1828_ = lean_ctor_get(v_a_1815_, 0);
lean_inc_ref(v_e_x27_1828_);
v_proof_1829_ = lean_ctor_get(v_a_1815_, 1);
lean_inc_ref(v_proof_1829_);
v_contextDependent_1830_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1815_, 2);
lean_inc_ref(v_p_1810_);
v___x_1831_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1810_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
lean_inc_ref(v_q_1811_);
v___x_1833_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1811_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v_a_1836_; lean_object* v___y_1845_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
if (lean_obj_tag(v_e_1778_) == 7)
{
lean_object* v_binderName_1855_; lean_object* v_binderType_1856_; lean_object* v_body_1857_; uint8_t v_binderInfo_1858_; size_t v___x_1859_; size_t v___x_1860_; uint8_t v___x_1861_; 
v_binderName_1855_ = lean_ctor_get(v_e_1778_, 0);
v_binderType_1856_ = lean_ctor_get(v_e_1778_, 1);
v_body_1857_ = lean_ctor_get(v_e_1778_, 2);
v_binderInfo_1858_ = lean_ctor_get_uint8(v_e_1778_, sizeof(void*)*3 + 8);
v___x_1859_ = lean_ptr_addr(v_binderType_1856_);
v___x_1860_ = lean_ptr_addr(v_p_1810_);
v___x_1861_ = lean_usize_dec_eq(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_inc(v_binderName_1855_);
lean_dec_ref_known(v_e_1778_, 3);
lean_inc_ref(v_e_x27_1828_);
lean_inc_ref(v_p_1810_);
v___x_1862_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1855_, v_binderInfo_1858_, v_p_1810_, v_e_x27_1828_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1845_ = v___x_1862_;
goto v___jp_1844_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = lean_ptr_addr(v_body_1857_);
v___x_1864_ = lean_ptr_addr(v_e_x27_1828_);
v___x_1865_ = lean_usize_dec_eq(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_inc(v_binderName_1855_);
lean_dec_ref_known(v_e_1778_, 3);
lean_inc_ref(v_e_x27_1828_);
lean_inc_ref(v_p_1810_);
v___x_1866_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1855_, v_binderInfo_1858_, v_p_1810_, v_e_x27_1828_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1845_ = v___x_1866_;
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
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec_ref(v_e_1778_);
v___x_1867_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1868_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1867_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1845_ = v___x_1868_;
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
v___x_1842_ = l_Lean_mkApp4(v___x_1841_, v_p_1810_, v_q_1811_, v_e_x27_1828_, v_proof_1829_);
v___x_1843_ = 0;
if (v_contextDependent_1827_ == 0)
{
v___y_1790_ = v_a_1836_;
v___y_1791_ = v___x_1843_;
v___y_1792_ = v___x_1842_;
v___y_1793_ = v_contextDependent_1830_;
goto v___jp_1789_;
}
else
{
v___y_1790_ = v_a_1836_;
v___y_1791_ = v___x_1843_;
v___y_1792_ = v___x_1842_;
v___y_1793_ = v_contextDependent_1827_;
goto v___jp_1789_;
}
}
v___jp_1844_:
{
if (lean_obj_tag(v___y_1845_) == 0)
{
lean_object* v_a_1846_; 
v_a_1846_ = lean_ctor_get(v___y_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___y_1845_, 1);
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
lean_dec_ref(v_q_1811_);
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
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_proof_1829_);
lean_dec_ref(v_e_x27_1828_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1869_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1833_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1833_);
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
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_proof_1829_);
lean_dec_ref(v_e_x27_1828_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1877_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1831_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1831_);
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
}
else
{
lean_del_object(v___x_1817_);
if (lean_obj_tag(v_a_1815_) == 0)
{
lean_object* v_e_x27_1885_; lean_object* v_proof_1886_; uint8_t v_contextDependent_1887_; uint8_t v_contextDependent_1888_; lean_object* v___x_1889_; 
v_e_x27_1885_ = lean_ctor_get(v_a_1813_, 0);
lean_inc_ref(v_e_x27_1885_);
v_proof_1886_ = lean_ctor_get(v_a_1813_, 1);
lean_inc_ref(v_proof_1886_);
v_contextDependent_1887_ = lean_ctor_get_uint8(v_a_1813_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1813_, 2);
v_contextDependent_1888_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref_known(v_a_1815_, 0);
lean_inc_ref(v_p_1810_);
v___x_1889_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1810_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
lean_inc_ref(v_q_1811_);
v___x_1891_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1811_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v_a_1894_; lean_object* v___y_1903_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
if (lean_obj_tag(v_e_1778_) == 7)
{
lean_object* v_binderName_1913_; lean_object* v_binderType_1914_; lean_object* v_body_1915_; uint8_t v_binderInfo_1916_; size_t v___x_1917_; size_t v___x_1918_; uint8_t v___x_1919_; 
v_binderName_1913_ = lean_ctor_get(v_e_1778_, 0);
v_binderType_1914_ = lean_ctor_get(v_e_1778_, 1);
v_body_1915_ = lean_ctor_get(v_e_1778_, 2);
v_binderInfo_1916_ = lean_ctor_get_uint8(v_e_1778_, sizeof(void*)*3 + 8);
v___x_1917_ = lean_ptr_addr(v_binderType_1914_);
v___x_1918_ = lean_ptr_addr(v_e_x27_1885_);
v___x_1919_ = lean_usize_dec_eq(v___x_1917_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; 
lean_inc(v_binderName_1913_);
lean_dec_ref_known(v_e_1778_, 3);
lean_inc_ref(v_q_1811_);
lean_inc_ref(v_e_x27_1885_);
v___x_1920_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1913_, v_binderInfo_1916_, v_e_x27_1885_, v_q_1811_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1903_ = v___x_1920_;
goto v___jp_1902_;
}
else
{
size_t v___x_1921_; size_t v___x_1922_; uint8_t v___x_1923_; 
v___x_1921_ = lean_ptr_addr(v_body_1915_);
v___x_1922_ = lean_ptr_addr(v_q_1811_);
v___x_1923_ = lean_usize_dec_eq(v___x_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_inc(v_binderName_1913_);
lean_dec_ref_known(v_e_1778_, 3);
lean_inc_ref(v_q_1811_);
lean_inc_ref(v_e_x27_1885_);
v___x_1924_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1913_, v_binderInfo_1916_, v_e_x27_1885_, v_q_1811_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1903_ = v___x_1924_;
goto v___jp_1902_;
}
else
{
v_a_1894_ = v_e_1778_;
goto v___jp_1893_;
}
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_e_1778_);
v___x_1925_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1926_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1925_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1903_ = v___x_1926_;
goto v___jp_1902_;
}
v___jp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1895_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__7));
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v_a_1892_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1890_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_mkConst(v___x_1895_, v___x_1898_);
v___x_1900_ = l_Lean_mkApp4(v___x_1899_, v_p_1810_, v_e_x27_1885_, v_q_1811_, v_proof_1886_);
v___x_1901_ = 0;
if (v_contextDependent_1887_ == 0)
{
v___y_1797_ = v___x_1900_;
v___y_1798_ = v___x_1901_;
v___y_1799_ = v_a_1894_;
v___y_1800_ = v_contextDependent_1888_;
goto v___jp_1796_;
}
else
{
v___y_1797_ = v___x_1900_;
v___y_1798_ = v___x_1901_;
v___y_1799_ = v_a_1894_;
v___y_1800_ = v_contextDependent_1887_;
goto v___jp_1796_;
}
}
v___jp_1902_:
{
if (lean_obj_tag(v___y_1903_) == 0)
{
lean_object* v_a_1904_; 
v_a_1904_ = lean_ctor_get(v___y_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___y_1903_, 1);
v_a_1894_ = v_a_1904_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_a_1892_);
lean_dec(v_a_1890_);
lean_dec_ref(v_proof_1886_);
lean_dec_ref(v_e_x27_1885_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
v_a_1905_ = lean_ctor_get(v___y_1903_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___y_1903_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___y_1903_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___y_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_a_1890_);
lean_dec_ref(v_proof_1886_);
lean_dec_ref(v_e_x27_1885_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1927_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1891_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1891_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v_proof_1886_);
lean_dec_ref(v_e_x27_1885_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1935_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1889_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1889_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_e_x27_1943_; lean_object* v_proof_1944_; uint8_t v_contextDependent_1945_; lean_object* v_e_x27_1946_; lean_object* v_proof_1947_; uint8_t v_contextDependent_1948_; lean_object* v___x_1949_; 
v_e_x27_1943_ = lean_ctor_get(v_a_1813_, 0);
lean_inc_ref(v_e_x27_1943_);
v_proof_1944_ = lean_ctor_get(v_a_1813_, 1);
lean_inc_ref(v_proof_1944_);
v_contextDependent_1945_ = lean_ctor_get_uint8(v_a_1813_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1813_, 2);
v_e_x27_1946_ = lean_ctor_get(v_a_1815_, 0);
lean_inc_ref(v_e_x27_1946_);
v_proof_1947_ = lean_ctor_get(v_a_1815_, 1);
lean_inc_ref(v_proof_1947_);
v_contextDependent_1948_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1815_, 2);
lean_inc_ref(v_p_1810_);
v___x_1949_ = l_Lean_Meta_Sym_getLevel___redArg(v_p_1810_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
lean_inc_ref(v_q_1811_);
v___x_1951_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_1811_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_a_1954_; lean_object* v___y_1963_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
if (lean_obj_tag(v_e_1778_) == 7)
{
lean_object* v_binderName_1973_; lean_object* v_binderType_1974_; lean_object* v_body_1975_; uint8_t v_binderInfo_1976_; size_t v___x_1977_; size_t v___x_1978_; uint8_t v___x_1979_; 
v_binderName_1973_ = lean_ctor_get(v_e_1778_, 0);
v_binderType_1974_ = lean_ctor_get(v_e_1778_, 1);
v_body_1975_ = lean_ctor_get(v_e_1778_, 2);
v_binderInfo_1976_ = lean_ctor_get_uint8(v_e_1778_, sizeof(void*)*3 + 8);
v___x_1977_ = lean_ptr_addr(v_binderType_1974_);
v___x_1978_ = lean_ptr_addr(v_e_x27_1943_);
v___x_1979_ = lean_usize_dec_eq(v___x_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_inc(v_binderName_1973_);
lean_dec_ref_known(v_e_1778_, 3);
lean_inc_ref(v_e_x27_1946_);
lean_inc_ref(v_e_x27_1943_);
v___x_1980_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1973_, v_binderInfo_1976_, v_e_x27_1943_, v_e_x27_1946_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1963_ = v___x_1980_;
goto v___jp_1962_;
}
else
{
size_t v___x_1981_; size_t v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = lean_ptr_addr(v_body_1975_);
v___x_1982_ = lean_ptr_addr(v_e_x27_1946_);
v___x_1983_ = lean_usize_dec_eq(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_inc(v_binderName_1973_);
lean_dec_ref_known(v_e_1778_, 3);
lean_inc_ref(v_e_x27_1946_);
lean_inc_ref(v_e_x27_1943_);
v___x_1984_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_1973_, v_binderInfo_1976_, v_e_x27_1943_, v_e_x27_1946_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1963_ = v___x_1984_;
goto v___jp_1962_;
}
else
{
v_a_1954_ = v_e_1778_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_e_1778_);
v___x_1985_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpArrow___closed__5, &l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5);
v___x_1986_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(v___x_1985_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
v___y_1963_ = v___x_1986_;
goto v___jp_1962_;
}
v___jp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1955_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpArrow___closed__9));
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1952_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1950_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = l_Lean_mkConst(v___x_1955_, v___x_1958_);
v___x_1960_ = l_Lean_mkApp6(v___x_1959_, v_p_1810_, v_e_x27_1943_, v_q_1811_, v_e_x27_1946_, v_proof_1944_, v_proof_1947_);
v___x_1961_ = 0;
if (v_contextDependent_1945_ == 0)
{
v___y_1804_ = v___x_1960_;
v___y_1805_ = v___x_1961_;
v___y_1806_ = v_a_1954_;
v___y_1807_ = v_contextDependent_1948_;
goto v___jp_1803_;
}
else
{
v___y_1804_ = v___x_1960_;
v___y_1805_ = v___x_1961_;
v___y_1806_ = v_a_1954_;
v___y_1807_ = v_contextDependent_1945_;
goto v___jp_1803_;
}
}
v___jp_1962_:
{
if (lean_obj_tag(v___y_1963_) == 0)
{
lean_object* v_a_1964_; 
v_a_1964_ = lean_ctor_get(v___y_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___y_1963_, 1);
v_a_1954_ = v_a_1964_;
goto v___jp_1953_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_a_1952_);
lean_dec(v_a_1950_);
lean_dec_ref(v_proof_1947_);
lean_dec_ref(v_e_x27_1946_);
lean_dec_ref(v_proof_1944_);
lean_dec_ref(v_e_x27_1943_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
v_a_1965_ = lean_ctor_get(v___y_1963_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___y_1963_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___y_1963_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___y_1963_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_a_1950_);
lean_dec_ref(v_proof_1947_);
lean_dec_ref(v_e_x27_1946_);
lean_dec_ref(v_proof_1944_);
lean_dec_ref(v_e_x27_1943_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1987_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1951_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1951_);
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
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_proof_1947_);
lean_dec_ref(v_e_x27_1946_);
lean_dec_ref(v_proof_1944_);
lean_dec_ref(v_e_x27_1943_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
v_a_1995_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1949_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1949_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
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
lean_dec(v_a_1813_);
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
return v___x_1814_;
}
}
else
{
lean_dec_ref(v_q_1811_);
lean_dec_ref(v_p_1810_);
lean_dec_ref(v_e_1778_);
return v___x_1812_;
}
v___jp_1789_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1794_, 0, v___y_1790_);
lean_ctor_set(v___x_1794_, 1, v___y_1792_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*2, v___y_1791_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*2 + 1, v___y_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
v___jp_1796_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1801_, 0, v___y_1799_);
lean_ctor_set(v___x_1801_, 1, v___y_1797_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*2, v___y_1798_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpArrow___boxed(lean_object* v_e_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Meta_Sym_Simp_simpArrow(v_e_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg(lean_object* v_u_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = l_Lean_Expr_sort___override(v_u_2016_);
v___x_2020_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2019_, v___y_2017_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg___boxed(lean_object* v_u_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg(v_u_2021_, v___y_2022_);
lean_dec(v___y_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0(lean_object* v_u_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg(v_u_2025_, v___y_2027_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___boxed(lean_object* v_u_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0(v_u_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg(lean_object* v_idx_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = l_Lean_Expr_bvar___override(v_idx_2043_);
v___x_2047_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2046_, v___y_2044_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg___boxed(lean_object* v_idx_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg(v_idx_2048_, v___y_2049_);
lean_dec(v___y_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1(lean_object* v_idx_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg(v_idx_2052_, v___y_2054_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___boxed(lean_object* v_idx_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1(v_idx_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__2(lean_object* v_x_2070_, uint8_t v_bi_2071_, lean_object* v_t_2072_, lean_object* v_b_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___y_2082_; lean_object* v___x_2085_; uint8_t v_debug_2086_; 
v___x_2085_ = lean_st_ref_get(v___y_2075_);
v_debug_2086_ = lean_ctor_get_uint8(v___x_2085_, sizeof(void*)*12);
lean_dec(v___x_2085_);
if (v_debug_2086_ == 0)
{
v___y_2082_ = v___y_2075_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2072_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2088_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_dec_ref_known(v___x_2088_, 1);
v___y_2082_ = v___y_2075_;
goto v___jp_2081_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_b_2073_);
lean_dec_ref(v_t_2072_);
lean_dec(v_x_2070_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
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
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_b_2073_);
lean_dec_ref(v_t_2072_);
lean_dec(v_x_2070_);
v_a_2097_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2087_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
v___jp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = l_Lean_Expr_lam___override(v_x_2070_, v_t_2072_, v_b_2073_, v_bi_2071_);
v___x_2084_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2083_, v___y_2082_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__2___boxed(lean_object* v_x_2105_, lean_object* v_bi_2106_, lean_object* v_t_2107_, lean_object* v_b_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v_bi_boxed_2116_; lean_object* v_res_2117_; 
v_bi_boxed_2116_ = lean_unbox(v_bi_2106_);
v_res_2117_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__2(v_x_2105_, v_bi_boxed_2116_, v_t_2107_, v_b_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4_spec__5(lean_object* v_f_2118_, lean_object* v_a_u2081_2119_, lean_object* v_a_u2082_2120_, lean_object* v_a_u2083_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_f_2118_, v_a_u2081_2119_, v_a_u2082_2120_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_2130_, v_a_u2083_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2131_;
}
else
{
lean_dec_ref(v_a_u2083_2121_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_f_2132_, lean_object* v_a_u2081_2133_, lean_object* v_a_u2082_2134_, lean_object* v_a_u2083_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4_spec__5(v_f_2132_, v_a_u2081_2133_, v_a_u2082_2134_, v_a_u2083_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4(lean_object* v_f_2144_, lean_object* v_a_u2081_2145_, lean_object* v_a_u2082_2146_, lean_object* v_a_u2083_2147_, lean_object* v_a_u2084_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4_spec__5(v_f_2144_, v_a_u2081_2145_, v_a_u2082_2146_, v_a_u2083_2147_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_2157_, v_a_u2084_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2158_;
}
else
{
lean_dec_ref(v_a_u2084_2148_);
return v___x_2156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4___boxed(lean_object* v_f_2159_, lean_object* v_a_u2081_2160_, lean_object* v_a_u2082_2161_, lean_object* v_a_u2083_2162_, lean_object* v_a_u2084_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4(v_f_2159_, v_a_u2081_2160_, v_a_u2082_2161_, v_a_u2083_2162_, v_a_u2084_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3(lean_object* v_f_2172_, lean_object* v_a_u2081_2173_, lean_object* v_a_u2082_2174_, lean_object* v_a_u2083_2175_, lean_object* v_a_u2084_2176_, lean_object* v_a_u2085_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3_spec__4(v_f_2172_, v_a_u2081_2173_, v_a_u2082_2174_, v_a_u2083_2175_, v_a_u2084_2176_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_2186_, v_a_u2085_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2187_;
}
else
{
lean_dec_ref(v_a_u2085_2177_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3___boxed(lean_object* v_f_2188_, lean_object* v_a_u2081_2189_, lean_object* v_a_u2082_2190_, lean_object* v_a_u2083_2191_, lean_object* v_a_u2084_2192_, lean_object* v_a_u2085_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3(v_f_2188_, v_a_u2081_2189_, v_a_u2082_2190_, v_a_u2083_2191_, v_a_u2084_2192_, v_a_u2085_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3(lean_object* v_f_2202_, lean_object* v_a_u2081_2203_, lean_object* v_a_u2082_2204_, lean_object* v_a_u2083_2205_, lean_object* v_a_u2084_2206_, lean_object* v_a_u2085_2207_, lean_object* v_a_u2086_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3_spec__3(v_f_2202_, v_a_u2081_2203_, v_a_u2082_2204_, v_a_u2083_2205_, v_a_u2084_2206_, v_a_u2085_2207_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_2217_, v_a_u2086_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2218_;
}
else
{
lean_dec_ref(v_a_u2086_2208_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3___boxed(lean_object* v_f_2219_, lean_object* v_a_u2081_2220_, lean_object* v_a_u2082_2221_, lean_object* v_a_u2083_2222_, lean_object* v_a_u2084_2223_, lean_object* v_a_u2085_2224_, lean_object* v_a_u2086_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3(v_f_2219_, v_a_u2081_2220_, v_a_u2082_2221_, v_a_u2083_2222_, v_a_u2084_2223_, v_a_u2085_2224_, v_a_u2086_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS(lean_object* v_p_u2081_2241_, lean_object* v_p_u2082_2242_, lean_object* v_h_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
v___x_2254_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__0___redArg(v___x_2253_, v_a_2246_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2256_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2256_ = l_Lean_Meta_Sym_shareCommon(v_h_2243_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__1));
v___x_2259_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
v___x_2260_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v___x_2258_, v___x_2259_, v_a_2246_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__1___redArg(v___x_2252_, v_a_2246_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___closed__3));
v___x_2265_ = 0;
lean_inc(v_a_2255_);
v___x_2266_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__2(v___x_2264_, v___x_2265_, v_a_2255_, v_a_2263_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS_spec__3(v_a_2261_, v_a_2255_, v_a_2267_, v_p_u2082_2242_, v_p_u2081_2241_, v_a_2257_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
return v___x_2268_;
}
else
{
lean_dec(v_a_2261_);
lean_dec(v_a_2257_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_p_u2082_2242_);
lean_dec_ref(v_p_u2081_2241_);
return v___x_2266_;
}
}
else
{
lean_dec(v_a_2261_);
lean_dec(v_a_2257_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_p_u2082_2242_);
lean_dec_ref(v_p_u2081_2241_);
return v___x_2262_;
}
}
else
{
lean_dec(v_a_2257_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_p_u2082_2242_);
lean_dec_ref(v_p_u2081_2241_);
return v___x_2260_;
}
}
else
{
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_p_u2082_2242_);
lean_dec_ref(v_p_u2081_2241_);
return v___x_2256_;
}
}
else
{
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_h_2243_);
lean_dec_ref(v_p_u2082_2242_);
lean_dec_ref(v_p_u2081_2241_);
return v___x_2254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS___boxed(lean_object* v_p_u2081_2269_, lean_object* v_p_u2082_2270_, lean_object* v_h_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS(v_p_u2081_2269_, v_p_u2082_2270_, v_h_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2280_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1(lean_object* v_msg_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_10050__overap_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___closed__0);
v___x_10050__overap_2294_ = lean_panic_fn_borrowed(v___x_2293_, v_msg_2282_);
lean_inc(v___y_2291_);
lean_inc_ref(v___y_2290_);
lean_inc(v___y_2289_);
lean_inc_ref(v___y_2288_);
lean_inc(v___y_2287_);
lean_inc_ref(v___y_2286_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2284_);
lean_inc(v___y_2283_);
v___x_2295_ = lean_apply_10(v___x_10050__overap_2294_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, lean_box(0));
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1___boxed(lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1(v_msg_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0(lean_object* v___y_2308_, lean_object* v_transientCache_2309_, lean_object* v_funext_2310_, lean_object* v_a_x3f_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v_numSteps_2314_; lean_object* v_persistentCache_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2325_; 
v___x_2313_ = lean_st_ref_take(v___y_2308_);
v_numSteps_2314_ = lean_ctor_get(v___x_2313_, 0);
v_persistentCache_2315_ = lean_ctor_get(v___x_2313_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; lean_object* v_unused_2327_; 
v_unused_2326_ = lean_ctor_get(v___x_2313_, 3);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v___x_2313_, 2);
lean_dec(v_unused_2327_);
v___x_2317_ = v___x_2313_;
v_isShared_2318_ = v_isSharedCheck_2325_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_persistentCache_2315_);
lean_inc(v_numSteps_2314_);
lean_dec(v___x_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2325_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_box(0);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 3, v_funext_2310_);
lean_ctor_set(v___x_2317_, 2, v_transientCache_2309_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_numSteps_2314_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_persistentCache_2315_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v_transientCache_2309_);
lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_funext_2310_);
v___x_2321_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_st_ref_put(v___y_2308_, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2319_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0___boxed(lean_object* v___y_2328_, lean_object* v_transientCache_2329_, lean_object* v_funext_2330_, lean_object* v_a_x3f_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0(v___y_2328_, v_transientCache_2329_, v_funext_2330_, v_a_x3f_2331_);
lean_dec(v_a_x3f_2331_);
lean_dec(v___y_2328_);
return v_res_2333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_box(0);
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__1));
v___x_2339_ = l_Lean_mkConst(v___x_2338_, v___x_2337_);
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__4));
v___x_2345_ = l_Lean_mkConst(v___x_2344_, v___x_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1(lean_object* v_binderType_2346_, lean_object* v_p_u2082_2347_, lean_object* v_h_2348_, lean_object* v_body_2349_, lean_object* v_simpBody_2350_, lean_object* v_q_u2081_2351_, lean_object* v_a_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v_transientCache_2364_; lean_object* v___x_2365_; lean_object* v_funext_2366_; lean_object* v_a_2368_; lean_object* v_a_2380_; lean_object* v___x_2391_; 
v___x_2363_ = lean_st_ref_get(v___y_2355_);
v_transientCache_2364_ = lean_ctor_get(v___x_2363_, 2);
lean_inc_ref(v_transientCache_2364_);
lean_dec(v___x_2363_);
v___x_2365_ = lean_st_ref_get(v___y_2355_);
v_funext_2366_ = lean_ctor_get(v___x_2365_, 3);
lean_inc_ref(v_funext_2366_);
lean_dec(v___x_2365_);
lean_inc_ref(v_a_2352_);
lean_inc_ref(v_h_2348_);
lean_inc_ref(v_p_u2082_2347_);
lean_inc_ref(v_binderType_2346_);
v___x_2391_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS(v_binderType_2346_, v_p_u2082_2347_, v_h_2348_, v_a_2352_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = lean_mk_empty_array_with_capacity(v___x_2393_);
lean_inc_ref(v___x_2394_);
v___x_2395_ = lean_array_push(v___x_2394_, v_a_2392_);
v___x_2396_ = l_Lean_Meta_Sym_instantiateS(v_body_2349_, v___x_2395_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc_n(v_a_2397_, 2);
lean_dec_ref_known(v___x_2396_, 1);
lean_inc(v___y_2361_);
lean_inc_ref(v___y_2360_);
lean_inc(v___y_2359_);
lean_inc_ref(v___y_2358_);
lean_inc(v___y_2357_);
lean_inc_ref(v___y_2356_);
lean_inc(v___y_2355_);
lean_inc_ref(v___y_2354_);
lean_inc(v___y_2353_);
v___x_2398_ = lean_apply_11(v_simpBody_2350_, v_a_2397_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, lean_box(0));
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
if (lean_obj_tag(v_a_2399_) == 0)
{
uint8_t v_contextDependent_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_contextDependent_2400_ = lean_ctor_get_uint8(v_a_2399_, 1);
lean_dec_ref_known(v_a_2399_, 0);
v___x_2401_ = lean_array_push(v___x_2394_, v_a_2352_);
v___x_2402_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_2401_, v_a_2397_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__2, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__2);
v___x_2405_ = l_Lean_mkApp4(v___x_2404_, v_binderType_2346_, v_p_u2082_2347_, v_h_2348_, v_q_u2081_2351_);
v___x_2406_ = 0;
v___x_2407_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2407_, 0, v_a_2403_);
lean_ctor_set(v___x_2407_, 1, v___x_2405_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*2, v___x_2406_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*2 + 1, v_contextDependent_2400_);
v_a_2380_ = v___x_2407_;
goto v___jp_2379_;
}
else
{
lean_object* v_a_2408_; 
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2408_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2402_, 1);
v_a_2368_ = v_a_2408_;
goto v___jp_2367_;
}
}
else
{
lean_object* v_e_x27_2409_; lean_object* v_proof_2410_; uint8_t v_contextDependent_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_a_2397_);
v_e_x27_2409_ = lean_ctor_get(v_a_2399_, 0);
v_proof_2410_ = lean_ctor_get(v_a_2399_, 1);
v_contextDependent_2411_ = lean_ctor_get_uint8(v_a_2399_, sizeof(void*)*2 + 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2413_ = v_a_2399_;
v_isShared_2414_ = v_isSharedCheck_2433_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_proof_2410_);
lean_inc(v_e_x27_2409_);
lean_dec(v_a_2399_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2433_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; uint8_t v___x_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; 
v___x_2415_ = lean_array_push(v___x_2394_, v_a_2352_);
v___x_2416_ = 0;
v___x_2417_ = 1;
v___x_2418_ = 1;
v___x_2419_ = l_Lean_Meta_mkLambdaFVars(v___x_2415_, v_proof_2410_, v___x_2416_, v___x_2417_, v___x_2416_, v___x_2417_, v___x_2418_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
lean_inc_ref(v_e_x27_2409_);
v___x_2421_ = l_Lean_Meta_mkLambdaFVars(v___x_2415_, v_e_x27_2409_, v___x_2416_, v___x_2417_, v___x_2416_, v___x_2417_, v___x_2418_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_2415_, v_e_x27_2409_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__5, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___closed__5);
v___x_2426_ = l_Lean_mkApp6(v___x_2425_, v_binderType_2346_, v_p_u2082_2347_, v_q_u2081_2351_, v_a_2422_, v_h_2348_, v_a_2420_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2426_);
lean_ctor_set(v___x_2413_, 0, v_a_2424_);
v___x_2428_ = v___x_2413_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2424_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, sizeof(void*)*2 + 1, v_contextDependent_2411_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*2, v___x_2416_);
v_a_2380_ = v___x_2428_;
goto v___jp_2379_;
}
}
else
{
lean_object* v_a_2430_; 
lean_dec(v_a_2422_);
lean_dec(v_a_2420_);
lean_del_object(v___x_2413_);
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2430_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2423_, 1);
v_a_2368_ = v_a_2430_;
goto v___jp_2367_;
}
}
else
{
lean_object* v_a_2431_; 
lean_dec(v_a_2420_);
lean_dec_ref(v___x_2415_);
lean_del_object(v___x_2413_);
lean_dec_ref(v_e_x27_2409_);
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2431_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2421_, 1);
v_a_2368_ = v_a_2431_;
goto v___jp_2367_;
}
}
else
{
lean_object* v_a_2432_; 
lean_dec_ref(v___x_2415_);
lean_del_object(v___x_2413_);
lean_dec_ref(v_e_x27_2409_);
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2432_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2419_, 1);
v_a_2368_ = v_a_2432_;
goto v___jp_2367_;
}
}
}
}
else
{
lean_object* v_a_2434_; 
lean_dec(v_a_2397_);
lean_dec_ref(v___x_2394_);
lean_dec_ref(v_a_2352_);
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2434_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2398_, 1);
v_a_2368_ = v_a_2434_;
goto v___jp_2367_;
}
}
else
{
lean_object* v_a_2435_; 
lean_dec_ref(v___x_2394_);
lean_dec_ref(v_a_2352_);
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_simpBody_2350_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2435_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2396_, 1);
v_a_2368_ = v_a_2435_;
goto v___jp_2367_;
}
}
else
{
lean_object* v_a_2436_; 
lean_dec_ref(v_a_2352_);
lean_dec_ref(v_q_u2081_2351_);
lean_dec_ref(v_simpBody_2350_);
lean_dec_ref(v_body_2349_);
lean_dec_ref(v_h_2348_);
lean_dec_ref(v_p_u2082_2347_);
lean_dec_ref(v_binderType_2346_);
v_a_2436_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2391_, 1);
v_a_2368_ = v_a_2436_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0(v___y_2355_, v_transientCache_2364_, v_funext_2366_, v___x_2369_);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; 
v_unused_2378_ = lean_ctor_get(v___x_2370_, 0);
lean_dec(v_unused_2378_);
v___x_2372_ = v___x_2370_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_dec(v___x_2370_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 1);
lean_ctor_set(v___x_2372_, 0, v_a_2368_);
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2368_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
v___jp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_inc_ref(v_a_2380_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2380_);
v___x_2382_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__0(v___y_2355_, v_transientCache_2364_, v_funext_2366_, v___x_2381_);
lean_dec_ref_known(v___x_2381_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2382_, 0);
lean_dec(v_unused_2390_);
v___x_2384_ = v___x_2382_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v___x_2382_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_a_2380_);
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2380_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___boxed(lean_object** _args){
lean_object* v_binderType_2437_ = _args[0];
lean_object* v_p_u2082_2438_ = _args[1];
lean_object* v_h_2439_ = _args[2];
lean_object* v_body_2440_ = _args[3];
lean_object* v_simpBody_2441_ = _args[4];
lean_object* v_q_u2081_2442_ = _args[5];
lean_object* v_a_2443_ = _args[6];
lean_object* v___y_2444_ = _args[7];
lean_object* v___y_2445_ = _args[8];
lean_object* v___y_2446_ = _args[9];
lean_object* v___y_2447_ = _args[10];
lean_object* v___y_2448_ = _args[11];
lean_object* v___y_2449_ = _args[12];
lean_object* v___y_2450_ = _args[13];
lean_object* v___y_2451_ = _args[14];
lean_object* v___y_2452_ = _args[15];
lean_object* v___y_2453_ = _args[16];
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1(v_binderType_2437_, v_p_u2082_2438_, v_h_2439_, v_body_2440_, v_simpBody_2441_, v_q_u2081_2442_, v_a_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg(lean_object* v_fvarId_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = l_Lean_Expr_fvar___override(v_fvarId_2455_);
v___x_2459_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2458_, v___y_2456_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg(v_fvarId_2460_, v___y_2461_);
lean_dec(v___y_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___lam__0(lean_object* v_k_2464_, lean_object* v_x_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = l_Lean_Expr_fvarId_x21(v_x_2465_);
v___x_2477_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg(v___x_2476_, v___y_2470_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
lean_inc(v___y_2474_);
lean_inc_ref(v___y_2473_);
lean_inc(v___y_2472_);
lean_inc_ref(v___y_2471_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc_ref(v___y_2467_);
lean_inc(v___y_2466_);
v___x_2479_ = lean_apply_11(v_k_2464_, v_a_2478_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, lean_box(0));
return v___x_2479_;
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec_ref(v_k_2464_);
v_a_2480_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2477_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2477_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___lam__0___boxed(lean_object* v_k_2488_, lean_object* v_x_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___lam__0(v_k_2488_, v_x_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v_x_2489_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___lam__0(lean_object* v_k_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v_b_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
v___x_2513_ = lean_apply_11(v_k_2501_, v_b_2507_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___lam__0(v_k_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v_b_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg(lean_object* v_name_2527_, uint8_t v_bi_2528_, lean_object* v_type_2529_, lean_object* v_k_2530_, uint8_t v_kind_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___f_2542_; lean_object* v___x_2543_; 
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2542_, 0, v_k_2530_);
lean_closure_set(v___f_2542_, 1, v___y_2532_);
lean_closure_set(v___f_2542_, 2, v___y_2533_);
lean_closure_set(v___f_2542_, 3, v___y_2534_);
lean_closure_set(v___f_2542_, 4, v___y_2535_);
lean_closure_set(v___f_2542_, 5, v___y_2536_);
v___x_2543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2527_, v_bi_2528_, v_type_2529_, v___f_2542_, v_kind_2531_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2543_) == 0)
{
return v___x_2543_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg___boxed(lean_object* v_name_2552_, lean_object* v_bi_2553_, lean_object* v_type_2554_, lean_object* v_k_2555_, lean_object* v_kind_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v_bi_boxed_2567_; uint8_t v_kind_boxed_2568_; lean_object* v_res_2569_; 
v_bi_boxed_2567_ = lean_unbox(v_bi_2553_);
v_kind_boxed_2568_ = lean_unbox(v_kind_2556_);
v_res_2569_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg(v_name_2552_, v_bi_boxed_2567_, v_type_2554_, v_k_2555_, v_kind_boxed_2568_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(lean_object* v_name_2570_, uint8_t v_bi_2571_, lean_object* v_type_2572_, lean_object* v_k_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___f_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; 
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2584_, 0, v_k_2573_);
v___x_2585_ = 0;
v___x_2586_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg(v_name_2570_, v_bi_2571_, v_type_2572_, v___f_2584_, v___x_2585_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg___boxed(lean_object* v_name_2587_, lean_object* v_bi_2588_, lean_object* v_type_2589_, lean_object* v_k_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
uint8_t v_bi_boxed_2601_; lean_object* v_res_2602_; 
v_bi_boxed_2601_ = lean_unbox(v_bi_2588_);
v_res_2602_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(v_name_2587_, v_bi_boxed_2601_, v_type_2589_, v_k_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
return v_res_2602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__3(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__2));
v___x_2607_ = lean_unsigned_to_nat(37u);
v___x_2608_ = lean_unsigned_to_nat(284u);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__1));
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__0));
v___x_2611_ = l_mkPanicMessageWithDecl(v___x_2610_, v___x_2609_, v___x_2608_, v___x_2607_, v___x_2606_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain(lean_object* v_simpBody_2612_, lean_object* v_e_2613_, lean_object* v_p_u2082_2614_, lean_object* v_h_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
if (lean_obj_tag(v_e_2613_) == 7)
{
lean_object* v_binderName_2626_; lean_object* v_binderType_2627_; lean_object* v_body_2628_; uint8_t v_binderInfo_2629_; lean_object* v_q_u2081_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; 
v_binderName_2626_ = lean_ctor_get(v_e_2613_, 0);
lean_inc_n(v_binderName_2626_, 2);
v_binderType_2627_ = lean_ctor_get(v_e_2613_, 1);
lean_inc_ref_n(v_binderType_2627_, 2);
v_body_2628_ = lean_ctor_get(v_e_2613_, 2);
lean_inc_ref_n(v_body_2628_, 2);
v_binderInfo_2629_ = lean_ctor_get_uint8(v_e_2613_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2613_, 3);
v_q_u2081_2630_ = l_Lean_mkLambda(v_binderName_2626_, v_binderInfo_2629_, v_binderType_2627_, v_body_2628_);
lean_inc_ref(v_p_u2082_2614_);
v___f_2631_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___lam__1___boxed), 17, 6);
lean_closure_set(v___f_2631_, 0, v_binderType_2627_);
lean_closure_set(v___f_2631_, 1, v_p_u2082_2614_);
lean_closure_set(v___f_2631_, 2, v_h_2615_);
lean_closure_set(v___f_2631_, 3, v_body_2628_);
lean_closure_set(v___f_2631_, 4, v_simpBody_2612_);
lean_closure_set(v___f_2631_, 5, v_q_u2081_2630_);
v___x_2632_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(v_binderName_2626_, v_binderInfo_2629_, v_p_u2082_2614_, v___f_2631_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec_ref(v_h_2615_);
lean_dec_ref(v_p_u2082_2614_);
lean_dec_ref(v_e_2613_);
lean_dec_ref(v_simpBody_2612_);
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__3, &l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___closed__3);
v___x_2634_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__1(v___x_2633_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain___boxed(lean_object* v_simpBody_2635_, lean_object* v_e_2636_, lean_object* v_p_u2082_2637_, lean_object* v_h_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain(v_simpBody_2635_, v_e_2636_, v_p_u2082_2637_, v_h_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0(lean_object* v_fvarId_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___redArg(v_fvarId_2650_, v___y_2652_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0___boxed(lean_object* v_fvarId_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__0(v_fvarId_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1(lean_object* v_00_u03b1_2668_, lean_object* v_name_2669_, uint8_t v_bi_2670_, lean_object* v_type_2671_, lean_object* v_k_2672_, uint8_t v_kind_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___redArg(v_name_2669_, v_bi_2670_, v_type_2671_, v_k_2672_, v_kind_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2685_, lean_object* v_name_2686_, lean_object* v_bi_2687_, lean_object* v_type_2688_, lean_object* v_k_2689_, lean_object* v_kind_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v_bi_boxed_2701_; uint8_t v_kind_boxed_2702_; lean_object* v_res_2703_; 
v_bi_boxed_2701_ = lean_unbox(v_bi_2687_);
v_kind_boxed_2702_ = lean_unbox(v_kind_2690_);
v_res_2703_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0_spec__1(v_00_u03b1_2685_, v_name_2686_, v_bi_boxed_2701_, v_type_2688_, v_k_2689_, v_kind_boxed_2702_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0(lean_object* v_00_u03b1_2704_, lean_object* v_name_2705_, uint8_t v_bi_2706_, lean_object* v_type_2707_, lean_object* v_k_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(v_name_2705_, v_bi_2706_, v_type_2707_, v_k_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_name_2721_, lean_object* v_bi_2722_, lean_object* v_type_2723_, lean_object* v_k_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
uint8_t v_bi_boxed_2735_; lean_object* v_res_2736_; 
v_bi_boxed_2735_ = lean_unbox(v_bi_2722_);
v_res_2736_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0(v_00_u03b1_2720_, v_name_2721_, v_bi_boxed_2735_, v_type_2723_, v_k_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(lean_object* v_xs_2737_, lean_object* v_b_2738_, lean_object* v_r_2739_, uint8_t v_cd_u2080_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
uint8_t v___y_2749_; 
if (lean_obj_tag(v_r_2739_) == 0)
{
lean_dec_ref(v_b_2738_);
lean_dec_ref(v_xs_2737_);
if (v_cd_u2080_2740_ == 0)
{
uint8_t v_contextDependent_2752_; 
v_contextDependent_2752_ = lean_ctor_get_uint8(v_r_2739_, 1);
lean_dec_ref_known(v_r_2739_, 0);
v___y_2749_ = v_contextDependent_2752_;
goto v___jp_2748_;
}
else
{
lean_dec_ref_known(v_r_2739_, 0);
v___y_2749_ = v_cd_u2080_2740_;
goto v___jp_2748_;
}
}
else
{
lean_object* v_e_x27_2753_; lean_object* v_proof_2754_; uint8_t v_done_2755_; uint8_t v_contextDependent_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2842_; 
v_e_x27_2753_ = lean_ctor_get(v_r_2739_, 0);
v_proof_2754_ = lean_ctor_get(v_r_2739_, 1);
v_done_2755_ = lean_ctor_get_uint8(v_r_2739_, sizeof(void*)*2);
v_contextDependent_2756_ = lean_ctor_get_uint8(v_r_2739_, sizeof(void*)*2 + 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_r_2739_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2758_ = v_r_2739_;
v_isShared_2759_ = v_isSharedCheck_2842_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_proof_2754_);
lean_inc(v_e_x27_2753_);
lean_dec(v_r_2739_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2842_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
uint8_t v___y_2761_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; uint8_t v___x_2769_; 
v___x_2766_ = lean_array_get_size(v_xs_2737_);
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = lean_nat_dec_eq(v___x_2766_, v___x_2767_);
v___x_2769_ = 1;
if (v___x_2768_ == 0)
{
uint8_t v___x_2770_; lean_object* v___x_2771_; 
lean_del_object(v___x_2758_);
v___x_2770_ = 1;
v___x_2771_ = l_Lean_Meta_mkLambdaFVars(v_xs_2737_, v_proof_2754_, v___x_2768_, v___x_2769_, v___x_2768_, v___x_2769_, v___x_2770_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
lean_inc_ref(v_e_x27_2753_);
v___x_2773_ = l_Lean_Meta_mkForallFVars(v_xs_2737_, v_e_x27_2753_, v___x_2768_, v___x_2769_, v___x_2769_, v___x_2770_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = l_Lean_Meta_Sym_shareCommon(v_a_2774_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
lean_inc_ref(v_xs_2737_);
v___x_2777_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_2737_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = l_Lean_Meta_mkLambdaFVars(v_xs_2737_, v_b_2738_, v___x_2768_, v___x_2769_, v___x_2768_, v___x_2769_, v___x_2770_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = l_Lean_Meta_mkLambdaFVars(v_xs_2737_, v_e_x27_2753_, v___x_2768_, v___x_2769_, v___x_2768_, v___x_2769_, v___x_2770_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
lean_dec_ref(v_xs_2737_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2793_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2793_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2793_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; uint8_t v___y_2788_; 
v___x_2786_ = l_Lean_mkApp3(v_a_2778_, v_a_2780_, v_a_2782_, v_a_2772_);
if (v_cd_u2080_2740_ == 0)
{
v___y_2788_ = v_contextDependent_2756_;
goto v___jp_2787_;
}
else
{
v___y_2788_ = v___x_2769_;
goto v___jp_2787_;
}
v___jp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2789_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2789_, 0, v_a_2776_);
lean_ctor_set(v___x_2789_, 1, v___x_2786_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*2, v___x_2768_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*2 + 1, v___y_2788_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2789_);
v___x_2791_ = v___x_2784_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_a_2780_);
lean_dec(v_a_2778_);
lean_dec(v_a_2776_);
lean_dec(v_a_2772_);
v_a_2794_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2781_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2781_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2778_);
lean_dec(v_a_2776_);
lean_dec(v_a_2772_);
lean_dec_ref(v_e_x27_2753_);
lean_dec_ref(v_xs_2737_);
v_a_2802_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2779_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2779_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2772_);
lean_dec_ref(v_e_x27_2753_);
lean_dec_ref(v_b_2738_);
lean_dec_ref(v_xs_2737_);
v_a_2810_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2777_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2777_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_a_2772_);
lean_dec_ref(v_e_x27_2753_);
lean_dec_ref(v_b_2738_);
lean_dec_ref(v_xs_2737_);
v_a_2818_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2775_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2775_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2772_);
lean_dec_ref(v_e_x27_2753_);
lean_dec_ref(v_b_2738_);
lean_dec_ref(v_xs_2737_);
v_a_2826_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2773_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2773_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref(v_e_x27_2753_);
lean_dec_ref(v_b_2738_);
lean_dec_ref(v_xs_2737_);
v_a_2834_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2771_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2771_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_dec_ref(v_b_2738_);
lean_dec_ref(v_xs_2737_);
if (v_cd_u2080_2740_ == 0)
{
v___y_2761_ = v_contextDependent_2756_;
goto v___jp_2760_;
}
else
{
v___y_2761_ = v___x_2769_;
goto v___jp_2760_;
}
}
v___jp_2760_:
{
lean_object* v___x_2763_; 
if (v_isShared_2759_ == 0)
{
v___x_2763_ = v___x_2758_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_e_x27_2753_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_proof_2754_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*2, v_done_2755_);
v___x_2763_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; 
lean_ctor_set_uint8(v___x_2763_, sizeof(void*)*2 + 1, v___y_2761_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
return v___x_2764_;
}
}
}
}
v___jp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2749_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg___boxed(lean_object* v_xs_2843_, lean_object* v_b_2844_, lean_object* v_r_2845_, lean_object* v_cd_u2080_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
uint8_t v_cd_u2080_boxed_2854_; lean_object* v_res_2855_; 
v_cd_u2080_boxed_2854_ = lean_unbox(v_cd_u2080_2846_);
v_res_2855_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(v_xs_2843_, v_b_2844_, v_r_2845_, v_cd_u2080_boxed_2854_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr(lean_object* v_xs_2856_, lean_object* v_b_2857_, lean_object* v_r_2858_, uint8_t v_cd_u2080_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(v_xs_2856_, v_b_2857_, v_r_2858_, v_cd_u2080_2859_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___boxed(lean_object* v_xs_2871_, lean_object* v_b_2872_, lean_object* v_r_2873_, lean_object* v_cd_u2080_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
uint8_t v_cd_u2080_boxed_2885_; lean_object* v_res_2886_; 
v_cd_u2080_boxed_2885_ = lean_unbox(v_cd_u2080_2874_);
v_res_2886_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr(v_xs_2871_, v_b_2872_, v_r_2873_, v_cd_u2080_boxed_2885_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0(lean_object* v_a_2887_, lean_object* v_transientCache_2888_, lean_object* v_funext_2889_, lean_object* v_a_x3f_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v_numSteps_2893_; lean_object* v_persistentCache_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2904_; 
v___x_2892_ = lean_st_ref_take(v_a_2887_);
v_numSteps_2893_ = lean_ctor_get(v___x_2892_, 0);
v_persistentCache_2894_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; lean_object* v_unused_2906_; 
v_unused_2905_ = lean_ctor_get(v___x_2892_, 3);
lean_dec(v_unused_2905_);
v_unused_2906_ = lean_ctor_get(v___x_2892_, 2);
lean_dec(v_unused_2906_);
v___x_2896_ = v___x_2892_;
v_isShared_2897_ = v_isSharedCheck_2904_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_persistentCache_2894_);
lean_inc(v_numSteps_2893_);
lean_dec(v___x_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2904_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = lean_box(0);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 3, v_funext_2889_);
lean_ctor_set(v___x_2896_, 2, v_transientCache_2888_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_numSteps_2893_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_persistentCache_2894_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_transientCache_2888_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_funext_2889_);
v___x_2900_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_st_ref_put(v_a_2887_, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2898_);
return v___x_2902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0___boxed(lean_object* v_a_2907_, lean_object* v_transientCache_2908_, lean_object* v_funext_2909_, lean_object* v_a_x3f_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0(v_a_2907_, v_transientCache_2908_, v_funext_2909_, v_a_x3f_2910_);
lean_dec(v_a_x3f_2910_);
lean_dec(v_a_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg(lean_object* v_xs_2913_, lean_object* v_k_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2925_ = lean_array_get_size(v_xs_2913_);
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = lean_nat_dec_eq(v___x_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v_transientCache_2929_; lean_object* v___x_2930_; lean_object* v_funext_2931_; lean_object* v_r_2932_; 
v___x_2928_ = lean_st_ref_get(v_a_2917_);
v_transientCache_2929_ = lean_ctor_get(v___x_2928_, 2);
lean_inc_ref(v_transientCache_2929_);
lean_dec(v___x_2928_);
v___x_2930_ = lean_st_ref_get(v_a_2917_);
v_funext_2931_ = lean_ctor_get(v___x_2930_, 3);
lean_inc_ref(v_funext_2931_);
lean_dec(v___x_2930_);
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
v_r_2932_ = lean_apply_10(v_k_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, lean_box(0));
if (lean_obj_tag(v_r_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2949_; 
v_a_2933_ = lean_ctor_get(v_r_2932_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_r_2932_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2935_ = v_r_2932_;
v_isShared_2936_ = v_isSharedCheck_2949_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v_r_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2949_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
lean_inc(v_a_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 1);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v___x_2939_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0(v_a_2917_, v_transientCache_2929_, v_funext_2931_, v___x_2938_);
lean_dec_ref(v___x_2938_);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v___x_2939_, 0);
lean_dec(v_unused_2947_);
v___x_2941_ = v___x_2939_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_dec(v___x_2939_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v_a_2933_);
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2933_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2950_ = lean_ctor_get(v_r_2932_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v_r_2932_, 1);
v___x_2951_ = lean_box(0);
v___x_2952_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___lam__0(v_a_2917_, v_transientCache_2929_, v_funext_2931_, v___x_2951_);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v___x_2952_, 0);
lean_dec(v_unused_2960_);
v___x_2954_ = v___x_2952_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v___x_2952_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 1);
lean_ctor_set(v___x_2954_, 0, v_a_2950_);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2950_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v___x_2961_; 
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
v___x_2961_ = lean_apply_10(v_k_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, lean_box(0));
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg___boxed(lean_object* v_xs_2962_, lean_object* v_k_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg(v_xs_2962_, v_k_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_xs_2962_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under(lean_object* v_00_u03b1_2975_, lean_object* v_xs_2976_, lean_object* v_k_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg(v_xs_2976_, v_k_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_xs_2990_, lean_object* v_k_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under(v_00_u03b1_2989_, v_xs_2990_, v_k_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_xs_2990_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(lean_object* v_xs_3003_, lean_object* v_e_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_array_get_size(v_xs_3003_);
v___x_3014_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_3004_, v___x_3012_, v___x_3013_, v_xs_3003_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg___boxed(lean_object* v_xs_3015_, lean_object* v_e_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(v_xs_3015_, v_e_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close(lean_object* v_xs_3025_, lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(v_xs_3025_, v_e_3026_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___boxed(lean_object* v_xs_3038_, lean_object* v_e_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close(v_xs_3038_, v_e_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___lam__0___boxed(lean_object* v_xs_3051_, lean_object* v_simpBody_3052_, lean_object* v_body_3053_, lean_object* v_cd_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
uint8_t v_cd_boxed_3066_; lean_object* v_res_3067_; 
v_cd_boxed_3066_ = lean_unbox(v_cd_3054_);
v_res_3067_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___lam__0(v_xs_3051_, v_simpBody_3052_, v_body_3053_, v_cd_boxed_3066_, v_x_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go(lean_object* v_simpBody_3068_, lean_object* v_xs_3069_, lean_object* v_e_3070_, uint8_t v_cd_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; 
if (lean_obj_tag(v_e_3070_) == 7)
{
lean_object* v_binderName_3106_; lean_object* v_binderType_3107_; lean_object* v_body_3108_; uint8_t v_binderInfo_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_binderName_3106_ = lean_ctor_get(v_e_3070_, 0);
v_binderType_3107_ = lean_ctor_get(v_e_3070_, 1);
v_body_3108_ = lean_ctor_get(v_e_3070_, 2);
v_binderInfo_3109_ = lean_ctor_get_uint8(v_e_3070_, sizeof(void*)*3 + 8);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_expr_has_loose_bvar(v_body_3108_, v___x_3110_);
if (v___x_3111_ == 0)
{
v___y_3083_ = v_a_3072_;
v___y_3084_ = v_a_3073_;
v___y_3085_ = v_a_3074_;
v___y_3086_ = v_a_3075_;
v___y_3087_ = v_a_3076_;
v___y_3088_ = v_a_3077_;
v___y_3089_ = v_a_3078_;
v___y_3090_ = v_a_3079_;
v___y_3091_ = v_a_3080_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3112_; 
lean_inc_ref(v_binderType_3107_);
lean_inc_ref(v_xs_3069_);
v___x_3112_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(v_xs_3069_, v_binderType_3107_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; uint8_t v_cd_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___x_3128_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_n(v_a_3113_, 2);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3128_ = l_Lean_Meta_isProp(v_a_3113_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; uint8_t v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v___x_3130_ = lean_unbox(v_a_3129_);
lean_dec(v_a_3129_);
if (v___x_3130_ == 0)
{
lean_inc_ref(v_body_3108_);
lean_inc(v_binderName_3106_);
lean_dec_ref_known(v_e_3070_, 3);
v_cd_3115_ = v_cd_3071_;
v___y_3116_ = v_a_3072_;
v___y_3117_ = v_a_3073_;
v___y_3118_ = v_a_3074_;
v___y_3119_ = v_a_3075_;
v___y_3120_ = v_a_3076_;
v___y_3121_ = v_a_3077_;
v___y_3122_ = v_a_3078_;
v___y_3123_ = v_a_3079_;
v___y_3124_ = v_a_3080_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_inc(v_a_3113_);
v___x_3131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3131_, 0, v_a_3113_);
v___x_3132_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg(v_xs_3069_, v___x_3131_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
if (lean_obj_tag(v_a_3133_) == 0)
{
lean_inc_ref(v_body_3108_);
lean_inc(v_binderName_3106_);
lean_dec_ref_known(v_e_3070_, 3);
if (v_cd_3071_ == 0)
{
uint8_t v_contextDependent_3134_; 
v_contextDependent_3134_ = lean_ctor_get_uint8(v_a_3133_, 1);
lean_dec_ref_known(v_a_3133_, 0);
v_cd_3115_ = v_contextDependent_3134_;
v___y_3116_ = v_a_3072_;
v___y_3117_ = v_a_3073_;
v___y_3118_ = v_a_3074_;
v___y_3119_ = v_a_3075_;
v___y_3120_ = v_a_3076_;
v___y_3121_ = v_a_3077_;
v___y_3122_ = v_a_3078_;
v___y_3123_ = v_a_3079_;
v___y_3124_ = v_a_3080_;
goto v___jp_3114_;
}
else
{
lean_dec_ref_known(v_a_3133_, 0);
v_cd_3115_ = v___x_3111_;
v___y_3116_ = v_a_3072_;
v___y_3117_ = v_a_3073_;
v___y_3118_ = v_a_3074_;
v___y_3119_ = v_a_3075_;
v___y_3120_ = v_a_3076_;
v___y_3121_ = v_a_3077_;
v___y_3122_ = v_a_3078_;
v___y_3123_ = v_a_3079_;
v___y_3124_ = v_a_3080_;
goto v___jp_3114_;
}
}
else
{
lean_object* v_e_x27_3135_; lean_object* v_proof_3136_; uint8_t v_contextDependent_3137_; lean_object* v___x_3138_; 
lean_dec(v_a_3113_);
v_e_x27_3135_ = lean_ctor_get(v_a_3133_, 0);
lean_inc_ref(v_e_x27_3135_);
v_proof_3136_ = lean_ctor_get(v_a_3133_, 1);
lean_inc_ref(v_proof_3136_);
v_contextDependent_3137_ = lean_ctor_get_uint8(v_a_3133_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3133_, 2);
lean_inc_ref(v_xs_3069_);
v___x_3138_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(v_xs_3069_, v_e_3070_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_n(v_a_3139_, 2);
lean_dec_ref_known(v___x_3138_, 1);
v___x_3140_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain(v_simpBody_3068_, v_a_3139_, v_e_x27_3135_, v_proof_3136_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
if (lean_obj_tag(v___x_3140_) == 0)
{
if (v_cd_3071_ == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(v_xs_3069_, v_a_3139_, v_a_3141_, v_contextDependent_3137_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
return v___x_3142_;
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3144_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(v_xs_3069_, v_a_3139_, v_a_3143_, v___x_3111_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
return v___x_3144_;
}
}
else
{
lean_dec(v_a_3139_);
lean_dec_ref(v_xs_3069_);
return v___x_3140_;
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v_proof_3136_);
lean_dec_ref(v_e_x27_3135_);
lean_dec_ref(v_xs_3069_);
lean_dec_ref(v_simpBody_3068_);
v_a_3145_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3138_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3138_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
else
{
lean_dec(v_a_3113_);
lean_dec_ref_known(v_e_3070_, 3);
lean_dec_ref(v_xs_3069_);
lean_dec_ref(v_simpBody_3068_);
return v___x_3132_;
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_a_3113_);
lean_dec_ref_known(v_e_3070_, 3);
lean_dec_ref(v_xs_3069_);
lean_dec_ref(v_simpBody_3068_);
v_a_3153_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3128_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3128_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
v___jp_3114_:
{
lean_object* v___x_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_box(v_cd_3115_);
v___f_3126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___lam__0___boxed), 15, 4);
lean_closure_set(v___f_3126_, 0, v_xs_3069_);
lean_closure_set(v___f_3126_, 1, v_simpBody_3068_);
lean_closure_set(v___f_3126_, 2, v_body_3108_);
lean_closure_set(v___f_3126_, 3, v___x_3125_);
v___x_3127_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(v_binderName_3106_, v_binderInfo_3109_, v_a_3113_, v___f_3126_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3127_;
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref_known(v_e_3070_, 3);
lean_dec_ref(v_xs_3069_);
lean_dec_ref(v_simpBody_3068_);
v_a_3161_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3112_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3112_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
else
{
v___y_3083_ = v_a_3072_;
v___y_3084_ = v_a_3073_;
v___y_3085_ = v_a_3074_;
v___y_3086_ = v_a_3075_;
v___y_3087_ = v_a_3076_;
v___y_3088_ = v_a_3077_;
v___y_3089_ = v_a_3078_;
v___y_3090_ = v_a_3079_;
v___y_3091_ = v_a_3080_;
goto v___jp_3082_;
}
v___jp_3082_:
{
lean_object* v___x_3092_; 
lean_inc_ref(v_xs_3069_);
v___x_3092_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_close___redArg(v_xs_3069_, v_e_3070_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc_n(v_a_3093_, 2);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = lean_apply_1(v_simpBody_3068_, v_a_3093_);
v___x_3095_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_under___redArg(v_xs_3069_, v___x_3094_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_mkCongr___redArg(v_xs_3069_, v_a_3093_, v_a_3096_, v_cd_3071_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3097_;
}
else
{
lean_dec(v_a_3093_);
lean_dec_ref(v_xs_3069_);
return v___x_3095_;
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v_xs_3069_);
lean_dec_ref(v_simpBody_3068_);
v_a_3098_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3092_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3092_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___lam__0(lean_object* v_xs_3169_, lean_object* v_simpBody_3170_, lean_object* v_body_3171_, uint8_t v_cd_3172_, lean_object* v_x_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_array_push(v_xs_3169_, v_x_3173_);
v___x_3185_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go(v_simpBody_3170_, v___x_3184_, v_body_3171_, v_cd_3172_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go___boxed(lean_object* v_simpBody_3186_, lean_object* v_xs_3187_, lean_object* v_e_3188_, lean_object* v_cd_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
uint8_t v_cd_boxed_3200_; lean_object* v_res_3201_; 
v_cd_boxed_3200_ = lean_unbox(v_cd_3189_);
v_res_3201_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go(v_simpBody_3186_, v_xs_3187_, v_e_3188_, v_cd_boxed_3200_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27(lean_object* v_simpArrow_3204_, lean_object* v_simpBody_3205_, lean_object* v_e_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
uint8_t v___x_3217_; 
v___x_3217_ = l_Lean_Expr_isArrow(v_e_3206_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref(v_simpArrow_3204_);
lean_inc_ref(v_e_3206_);
v___x_3218_ = l_Lean_Meta_isProp(v_e_3206_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3232_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3232_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3232_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_unbox(v_a_3219_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; uint8_t v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3228_; 
lean_dec_ref(v_e_3206_);
lean_dec_ref(v_simpBody_3205_);
v___x_3224_ = lean_alloc_ctor(0, 0, 2);
v___x_3225_ = lean_unbox(v_a_3219_);
lean_ctor_set_uint8(v___x_3224_, 0, v___x_3225_);
v___x_3226_ = lean_unbox(v_a_3219_);
lean_dec(v_a_3219_);
lean_ctor_set_uint8(v___x_3224_, 1, v___x_3226_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3224_);
v___x_3228_ = v___x_3221_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3224_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_del_object(v___x_3221_);
lean_dec(v_a_3219_);
v___x_3230_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall_x27___closed__0));
v___x_3231_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_go(v_simpBody_3205_, v___x_3230_, v_e_3206_, v___x_3217_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
return v___x_3231_;
}
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v_e_3206_);
lean_dec_ref(v_simpBody_3205_);
v_a_3233_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3218_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3218_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
else
{
lean_object* v___x_3241_; 
lean_dec_ref(v_simpBody_3205_);
lean_inc(v_a_3215_);
lean_inc_ref(v_a_3214_);
lean_inc(v_a_3213_);
lean_inc_ref(v_a_3212_);
lean_inc(v_a_3211_);
lean_inc_ref(v_a_3210_);
lean_inc(v_a_3209_);
lean_inc_ref(v_a_3208_);
lean_inc(v_a_3207_);
v___x_3241_ = lean_apply_11(v_simpArrow_3204_, v_e_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, lean_box(0));
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(lean_object* v_simpArrow_3242_, lean_object* v_simpBody_3243_, lean_object* v_e_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v_simpArrow_3242_, v_simpBody_3243_, v_e_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___lam__0(lean_object* v_binderType_3256_, lean_object* v_e_x27_3257_, lean_object* v_proof_3258_, lean_object* v_body_3259_, lean_object* v_a_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; 
lean_inc_ref(v_a_3260_);
v___x_3271_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkPropDomainCastS(v_binderType_3256_, v_e_x27_3257_, v_proof_3258_, v_a_3260_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_mk_empty_array_with_capacity(v___x_3273_);
lean_inc_ref(v___x_3274_);
v___x_3275_ = lean_array_push(v___x_3274_, v_a_3272_);
v___x_3276_ = l_Lean_Meta_Sym_instantiateS(v_body_3259_, v___x_3275_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = lean_array_push(v___x_3274_, v_a_3260_);
v___x_3279_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v___x_3278_, v_a_3277_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
return v___x_3279_;
}
else
{
lean_dec_ref(v___x_3274_);
lean_dec_ref(v_a_3260_);
return v___x_3276_;
}
}
else
{
lean_dec_ref(v_a_3260_);
lean_dec_ref(v_body_3259_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___lam__0___boxed(lean_object* v_binderType_3280_, lean_object* v_e_x27_3281_, lean_object* v_proof_3282_, lean_object* v_body_3283_, lean_object* v_a_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Meta_Sym_Simp_simpExistsPropDomain___lam__0(v_binderType_3280_, v_e_x27_3281_, v_proof_3282_, v_body_3283_, v_a_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
return v_res_3295_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__5(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_box(0);
v___x_3305_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__4));
v___x_3306_ = l_Lean_mkConst(v___x_3305_, v___x_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain(lean_object* v_e_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = l_Lean_Expr_cleanupAnnotations(v_e_3307_);
v___x_3322_ = l_Lean_Expr_isApp(v___x_3321_);
if (v___x_3322_ == 0)
{
lean_dec_ref(v___x_3321_);
goto v___jp_3318_;
}
else
{
lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3321_);
v___x_3324_ = l_Lean_Expr_isApp(v___x_3323_);
if (v___x_3324_ == 0)
{
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3321_);
goto v___jp_3318_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3325_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3323_);
lean_dec_ref(v___x_3323_);
v___x_3326_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__2));
v___x_3327_ = l_Lean_Expr_isConstOf(v___x_3325_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3321_);
goto v___jp_3318_;
}
else
{
lean_object* v_arg_3328_; 
v_arg_3328_ = lean_ctor_get(v___x_3321_, 1);
lean_inc_ref(v_arg_3328_);
lean_dec_ref(v___x_3321_);
if (lean_obj_tag(v_arg_3328_) == 6)
{
lean_object* v_binderName_3329_; lean_object* v_binderType_3330_; lean_object* v_body_3331_; uint8_t v_binderInfo_3332_; lean_object* v___x_3333_; 
v_binderName_3329_ = lean_ctor_get(v_arg_3328_, 0);
v_binderType_3330_ = lean_ctor_get(v_arg_3328_, 1);
lean_inc_ref_n(v_binderType_3330_, 2);
v_body_3331_ = lean_ctor_get(v_arg_3328_, 2);
v_binderInfo_3332_ = lean_ctor_get_uint8(v_arg_3328_, sizeof(void*)*3 + 8);
v___x_3333_ = l_Lean_Meta_isProp(v_binderType_3330_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3397_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3397_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3397_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_unbox(v_a_3334_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; uint8_t v___x_3340_; uint8_t v___x_3341_; lean_object* v___x_3343_; 
lean_dec_ref(v_binderType_3330_);
lean_dec_ref_known(v_arg_3328_, 3);
lean_dec_ref(v___x_3325_);
v___x_3339_ = lean_alloc_ctor(0, 0, 2);
v___x_3340_ = lean_unbox(v_a_3334_);
lean_ctor_set_uint8(v___x_3339_, 0, v___x_3340_);
v___x_3341_ = lean_unbox(v_a_3334_);
lean_dec(v_a_3334_);
lean_ctor_set_uint8(v___x_3339_, 1, v___x_3341_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3339_);
v___x_3343_ = v___x_3336_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3339_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
lean_object* v___x_3345_; 
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
lean_inc(v_a_3314_);
lean_inc_ref(v_a_3313_);
lean_inc(v_a_3312_);
lean_inc_ref(v_a_3311_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_binderType_3330_);
v___x_3345_ = lean_sym_simp(v_binderType_3330_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3396_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3396_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3396_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
if (lean_obj_tag(v_a_3346_) == 0)
{
uint8_t v_contextDependent_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
lean_dec_ref(v_binderType_3330_);
lean_dec_ref_known(v_arg_3328_, 3);
lean_dec_ref(v___x_3325_);
v_contextDependent_3350_ = lean_ctor_get_uint8(v_a_3346_, 1);
lean_dec_ref_known(v_a_3346_, 0);
v___x_3351_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_3350_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3351_);
v___x_3353_ = v___x_3348_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
else
{
lean_object* v_e_x27_3355_; lean_object* v_proof_3356_; uint8_t v_contextDependent_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3395_; 
lean_del_object(v___x_3348_);
v_e_x27_3355_ = lean_ctor_get(v_a_3346_, 0);
v_proof_3356_ = lean_ctor_get(v_a_3346_, 1);
v_contextDependent_3357_ = lean_ctor_get_uint8(v_a_3346_, sizeof(void*)*2 + 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3346_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3359_ = v_a_3346_;
v_isShared_3360_ = v_isSharedCheck_3395_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_proof_3356_);
lean_inc(v_e_x27_3355_);
lean_dec(v_a_3346_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3395_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___f_3361_; lean_object* v___x_3362_; 
lean_inc_ref(v_body_3331_);
lean_inc_ref(v_proof_3356_);
lean_inc_ref_n(v_e_x27_3355_, 2);
lean_inc_ref(v_binderType_3330_);
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpExistsPropDomain___lam__0___boxed), 15, 4);
lean_closure_set(v___f_3361_, 0, v_binderType_3330_);
lean_closure_set(v___f_3361_, 1, v_e_x27_3355_);
lean_closure_set(v___f_3361_, 2, v_proof_3356_);
lean_closure_set(v___f_3361_, 3, v_body_3331_);
lean_inc(v_binderName_3329_);
v___x_3362_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_simpPropDomain_spec__0___redArg(v_binderName_3329_, v_binderInfo_3332_, v_e_x27_3355_, v___f_3361_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
lean_inc_ref(v_e_x27_3355_);
v___x_3364_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_3325_, v_e_x27_3355_, v_a_3363_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3378_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3378_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3378_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; lean_object* v___x_3373_; 
v___x_3369_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__5, &l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__5);
v___x_3370_ = l_Lean_mkApp4(v___x_3369_, v_binderType_3330_, v_e_x27_3355_, v_proof_3356_, v_arg_3328_);
v___x_3371_ = 0;
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3370_);
lean_ctor_set(v___x_3359_, 0, v_a_3365_);
v___x_3373_ = v___x_3359_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3365_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3377_, sizeof(void*)*2 + 1, v_contextDependent_3357_);
v___x_3373_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*2, v___x_3371_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3373_);
v___x_3375_ = v___x_3367_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_del_object(v___x_3359_);
lean_dec_ref(v_proof_3356_);
lean_dec_ref(v_e_x27_3355_);
lean_dec_ref(v_binderType_3330_);
lean_dec_ref_known(v_arg_3328_, 3);
v_a_3379_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3364_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3364_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_del_object(v___x_3359_);
lean_dec_ref(v_proof_3356_);
lean_dec_ref(v_e_x27_3355_);
lean_dec_ref(v_binderType_3330_);
lean_dec_ref_known(v_arg_3328_, 3);
lean_dec_ref(v___x_3325_);
v_a_3387_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3362_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3362_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_binderType_3330_);
lean_dec_ref_known(v_arg_3328_, 3);
lean_dec_ref(v___x_3325_);
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v_binderType_3330_);
lean_dec_ref_known(v_arg_3328_, 3);
lean_dec_ref(v___x_3325_);
v_a_3398_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3333_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3333_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_dec_ref(v_arg_3328_);
lean_dec_ref(v___x_3325_);
v___x_3406_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__0));
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
}
}
v___jp_3318_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpExistsPropDomain___closed__0));
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain___boxed(lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Meta_Sym_Simp_simpExistsPropDomain(v_e_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec_ref(v_e_3408_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object* v_e_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__0));
v___x_3434_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpForall___closed__1));
v___x_3435_ = l_Lean_Meta_Sym_Simp_simpForall_x27(v___x_3433_, v___x_3434_, v_e_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpForall___boxed(lean_object* v_e_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
return v_res_3447_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
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
