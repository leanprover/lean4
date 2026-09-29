// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM public import Lean.Meta.Sym.Arith.Poly public import Lean.Meta.Sym.Arith.SafePoly import Init.Data.Nat.Internal.Linear
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
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`grind` internal error, polynomial computation failed"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__47_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spolM_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spolM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spolM___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spolM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spolM___closed__1;
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spolM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spolM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2_value;
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__3_value;
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_toApplicative_22_; lean_object* v_toFunctor_23_; lean_object* v_toSeq_24_; lean_object* v_toSeqLeft_25_; lean_object* v_toSeqRight_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_toApplicative_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_98_; 
v___x_21_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_22_ = lean_ctor_get(v___x_21_, 0);
v_toFunctor_23_ = lean_ctor_get(v_toApplicative_22_, 0);
v_toSeq_24_ = lean_ctor_get(v_toApplicative_22_, 2);
v_toSeqLeft_25_ = lean_ctor_get(v_toApplicative_22_, 3);
v_toSeqRight_26_ = lean_ctor_get(v_toApplicative_22_, 4);
v___f_27_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_28_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_23_, 2);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_29_, 0, v_toFunctor_23_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_30_, 0, v_toFunctor_23_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___f_29_);
lean_ctor_set(v___x_31_, 1, v___f_30_);
lean_inc(v_toSeqRight_26_);
v___f_32_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_32_, 0, v_toSeqRight_26_);
lean_inc(v_toSeqLeft_25_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_33_, 0, v_toSeqLeft_25_);
lean_inc(v_toSeq_24_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_34_, 0, v_toSeq_24_);
v___x_35_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_35_, 0, v___x_31_);
lean_ctor_set(v___x_35_, 1, v___f_27_);
lean_ctor_set(v___x_35_, 2, v___f_34_);
lean_ctor_set(v___x_35_, 3, v___f_33_);
lean_ctor_set(v___x_35_, 4, v___f_32_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___f_28_);
v___x_37_ = l_StateRefT_x27_instMonad___redArg(v___x_36_);
v_toApplicative_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v___x_37_, 1);
lean_dec(v_unused_99_);
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_98_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_toApplicative_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_98_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v_toFunctor_42_; lean_object* v_toSeq_43_; lean_object* v_toSeqLeft_44_; lean_object* v_toSeqRight_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_96_; 
v_toFunctor_42_ = lean_ctor_get(v_toApplicative_38_, 0);
v_toSeq_43_ = lean_ctor_get(v_toApplicative_38_, 2);
v_toSeqLeft_44_ = lean_ctor_get(v_toApplicative_38_, 3);
v_toSeqRight_45_ = lean_ctor_get(v_toApplicative_38_, 4);
v_isSharedCheck_96_ = !lean_is_exclusive(v_toApplicative_38_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_toApplicative_38_, 1);
lean_dec(v_unused_97_);
v___x_47_ = v_toApplicative_38_;
v_isShared_48_ = v_isSharedCheck_96_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_toSeqRight_45_);
lean_inc(v_toSeqLeft_44_);
lean_inc(v_toSeq_43_);
lean_inc(v_toFunctor_42_);
lean_dec(v_toApplicative_38_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_96_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_58_; 
v___f_49_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_42_);
v___f_51_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_51_, 0, v_toFunctor_42_);
v___f_52_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_52_, 0, v_toFunctor_42_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___f_51_);
lean_ctor_set(v___x_53_, 1, v___f_52_);
v___f_54_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_54_, 0, v_toSeqRight_45_);
v___f_55_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_55_, 0, v_toSeqLeft_44_);
v___f_56_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_56_, 0, v_toSeq_43_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 4, v___f_54_);
lean_ctor_set(v___x_47_, 3, v___f_55_);
lean_ctor_set(v___x_47_, 2, v___f_56_);
lean_ctor_set(v___x_47_, 1, v___f_49_);
lean_ctor_set(v___x_47_, 0, v___x_53_);
v___x_58_ = v___x_47_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___f_49_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v___f_56_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v___f_55_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v___f_54_);
v___x_58_ = v_reuseFailAlloc_95_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_60_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v___f_50_);
lean_ctor_set(v___x_40_, 0, v___x_58_);
v___x_60_ = v___x_40_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___f_50_);
v___x_60_ = v_reuseFailAlloc_94_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toApplicative_69_; lean_object* v_toBind_70_; lean_object* v_getCommRing_71_; lean_object* v_modifyCommRing_72_; lean_object* v_toPure_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_714__overap_78_; lean_object* v___x_79_; 
v___x_61_ = l_StateRefT_x27_instMonad___redArg(v___x_60_);
v___x_62_ = l_ReaderT_instMonad___redArg(v___x_61_);
v___x_63_ = l_StateRefT_x27_instMonad___redArg(v___x_62_);
v___x_64_ = l_ReaderT_instMonad___redArg(v___x_63_);
v___x_65_ = l_ReaderT_instMonad___redArg(v___x_64_);
v___x_66_ = l_StateRefT_x27_instMonad___redArg(v___x_65_);
v___x_67_ = l_ReaderT_instMonad___redArg(v___x_66_);
v___x_68_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_69_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_toApplicative_69_);
v_toBind_70_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_toBind_70_);
v_getCommRing_71_ = lean_ctor_get(v___x_68_, 0);
v_modifyCommRing_72_ = lean_ctor_get(v___x_68_, 1);
v_toPure_73_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_73_);
lean_dec_ref(v_toApplicative_69_);
lean_inc(v_modifyCommRing_72_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_74_, 0, v_modifyCommRing_72_);
v___f_75_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_75_, 0, v_toPure_73_);
lean_inc(v_getCommRing_71_);
v___x_76_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v_getCommRing_71_, v___f_75_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___f_74_);
v___x_714__overap_78_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_67_, v___x_77_);
lean_inc(v_a_19_);
lean_inc_ref(v_a_18_);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
lean_inc(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
v___x_79_ = lean_apply_12(v___x_714__overap_78_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, lean_box(0));
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; uint8_t v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_79_, 1);
v___x_81_ = 0;
v___x_82_ = 1;
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_84_, 0, v_a_80_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
lean_ctor_set(v___x_84_, 2, v___x_83_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3, v___x_81_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 1, v___x_82_);
lean_inc(v_a_19_);
lean_inc_ref(v_a_18_);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
v___x_85_ = lean_apply_8(v_x_8_, v___x_84_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, lean_box(0));
return v___x_85_;
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v_x_8_);
v_a_86_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_79_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_79_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___boxed(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg(v_x_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly(lean_object* v_00_u03b1_114_, lean_object* v_x_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; lean_object* v_toApplicative_129_; lean_object* v_toFunctor_130_; lean_object* v_toSeq_131_; lean_object* v_toSeqLeft_132_; lean_object* v_toSeqRight_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_toApplicative_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_205_; 
v___x_128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_129_ = lean_ctor_get(v___x_128_, 0);
v_toFunctor_130_ = lean_ctor_get(v_toApplicative_129_, 0);
v_toSeq_131_ = lean_ctor_get(v_toApplicative_129_, 2);
v_toSeqLeft_132_ = lean_ctor_get(v_toApplicative_129_, 3);
v_toSeqRight_133_ = lean_ctor_get(v_toApplicative_129_, 4);
v___f_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_130_, 2);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_136_, 0, v_toFunctor_130_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_137_, 0, v_toFunctor_130_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___f_136_);
lean_ctor_set(v___x_138_, 1, v___f_137_);
lean_inc(v_toSeqRight_133_);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_139_, 0, v_toSeqRight_133_);
lean_inc(v_toSeqLeft_132_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_140_, 0, v_toSeqLeft_132_);
lean_inc(v_toSeq_131_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_141_, 0, v_toSeq_131_);
v___x_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_142_, 0, v___x_138_);
lean_ctor_set(v___x_142_, 1, v___f_134_);
lean_ctor_set(v___x_142_, 2, v___f_141_);
lean_ctor_set(v___x_142_, 3, v___f_140_);
lean_ctor_set(v___x_142_, 4, v___f_139_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___f_135_);
v___x_144_ = l_StateRefT_x27_instMonad___redArg(v___x_143_);
v_toApplicative_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v___x_144_, 1);
lean_dec(v_unused_206_);
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_205_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_toApplicative_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_205_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_toFunctor_149_; lean_object* v_toSeq_150_; lean_object* v_toSeqLeft_151_; lean_object* v_toSeqRight_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_203_; 
v_toFunctor_149_ = lean_ctor_get(v_toApplicative_145_, 0);
v_toSeq_150_ = lean_ctor_get(v_toApplicative_145_, 2);
v_toSeqLeft_151_ = lean_ctor_get(v_toApplicative_145_, 3);
v_toSeqRight_152_ = lean_ctor_get(v_toApplicative_145_, 4);
v_isSharedCheck_203_ = !lean_is_exclusive(v_toApplicative_145_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_toApplicative_145_, 1);
lean_dec(v_unused_204_);
v___x_154_ = v_toApplicative_145_;
v_isShared_155_ = v_isSharedCheck_203_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_toSeqRight_152_);
lean_inc(v_toSeqLeft_151_);
lean_inc(v_toSeq_150_);
lean_inc(v_toFunctor_149_);
lean_dec(v_toApplicative_145_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_203_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_165_; 
v___f_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_149_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_149_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_159_, 0, v_toFunctor_149_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___f_158_);
lean_ctor_set(v___x_160_, 1, v___f_159_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqRight_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeqLeft_151_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_163_, 0, v_toSeq_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 4, v___f_161_);
lean_ctor_set(v___x_154_, 3, v___f_162_);
lean_ctor_set(v___x_154_, 2, v___f_163_);
lean_ctor_set(v___x_154_, 1, v___f_156_);
lean_ctor_set(v___x_154_, 0, v___x_160_);
v___x_165_ = v___x_154_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___f_156_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v___f_163_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___f_162_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___f_161_);
v___x_165_ = v_reuseFailAlloc_202_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___f_157_);
lean_ctor_set(v___x_147_, 0, v___x_165_);
v___x_167_ = v___x_147_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___f_157_);
v___x_167_ = v_reuseFailAlloc_201_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_toApplicative_176_; lean_object* v_toBind_177_; lean_object* v_getCommRing_178_; lean_object* v_modifyCommRing_179_; lean_object* v_toPure_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_753__overap_185_; lean_object* v___x_186_; 
v___x_168_ = l_StateRefT_x27_instMonad___redArg(v___x_167_);
v___x_169_ = l_ReaderT_instMonad___redArg(v___x_168_);
v___x_170_ = l_StateRefT_x27_instMonad___redArg(v___x_169_);
v___x_171_ = l_ReaderT_instMonad___redArg(v___x_170_);
v___x_172_ = l_ReaderT_instMonad___redArg(v___x_171_);
v___x_173_ = l_StateRefT_x27_instMonad___redArg(v___x_172_);
v___x_174_ = l_ReaderT_instMonad___redArg(v___x_173_);
v___x_175_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_176_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_toApplicative_176_);
v_toBind_177_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_toBind_177_);
v_getCommRing_178_ = lean_ctor_get(v___x_175_, 0);
v_modifyCommRing_179_ = lean_ctor_get(v___x_175_, 1);
v_toPure_180_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_inc(v_toPure_180_);
lean_dec_ref(v_toApplicative_176_);
lean_inc(v_modifyCommRing_179_);
v___f_181_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_181_, 0, v_modifyCommRing_179_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_182_, 0, v_toPure_180_);
lean_inc(v_getCommRing_178_);
v___x_183_ = lean_apply_4(v_toBind_177_, lean_box(0), lean_box(0), v_getCommRing_178_, v___f_182_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___f_181_);
v___x_753__overap_185_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_174_, v___x_184_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
v___x_186_ = lean_apply_12(v___x_753__overap_185_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; uint8_t v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
v___x_188_ = 0;
v___x_189_ = 1;
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_191_, 0, v_a_187_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
lean_ctor_set(v___x_191_, 2, v___x_190_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*3, v___x_188_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*3 + 1, v___x_189_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
v___x_192_ = lean_apply_8(v_x_115_, v___x_191_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
return v___x_192_;
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_x_115_);
v_a_193_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_186_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_186_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___boxed(lean_object* v_00_u03b1_207_, lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly(v_00_u03b1_207_, v_x_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0(void){
_start:
{
lean_object* v___x_222_; lean_object* v___f_223_; 
v___x_222_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_223_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_223_, 0, v___x_222_);
return v___f_223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___f_225_; 
v___x_224_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_225_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_225_, 0, v___x_224_);
return v___f_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2(void){
_start:
{
lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; 
v___f_226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1);
v___f_227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___f_227_);
lean_ctor_set(v___x_228_, 1, v___f_226_);
return v___x_228_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_229_; lean_object* v___f_230_; 
v___x_229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_230_, 0, v___x_229_);
return v___f_230_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4(void){
_start:
{
lean_object* v___x_231_; lean_object* v___f_232_; 
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_232_, 0, v___x_231_);
return v___f_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5(void){
_start:
{
lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; 
v___f_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4);
v___f_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___f_234_);
lean_ctor_set(v___x_235_, 1, v___f_233_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6(void){
_start:
{
lean_object* v___x_236_; lean_object* v___f_237_; 
v___x_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5);
v___f_237_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_237_, 0, v___x_236_);
return v___f_237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7(void){
_start:
{
lean_object* v___x_238_; lean_object* v___f_239_; 
v___x_238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5);
v___f_239_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_239_, 0, v___x_238_);
return v___f_239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8(void){
_start:
{
lean_object* v___f_240_; lean_object* v___f_241_; lean_object* v___x_242_; 
v___f_240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7);
v___f_241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___f_241_);
lean_ctor_set(v___x_242_, 1, v___f_240_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9(void){
_start:
{
lean_object* v___x_243_; lean_object* v___f_244_; 
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8);
v___f_244_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_244_, 0, v___x_243_);
return v___f_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10(void){
_start:
{
lean_object* v___x_245_; lean_object* v___f_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8);
v___f_246_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_246_, 0, v___x_245_);
return v___f_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11(void){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; 
v___f_247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10);
v___f_248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___f_248_);
lean_ctor_set(v___x_249_, 1, v___f_247_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12(void){
_start:
{
lean_object* v___x_250_; lean_object* v___f_251_; 
v___x_250_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11);
v___f_251_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_251_, 0, v___x_250_);
return v___f_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13(void){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; 
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11);
v___f_253_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
return v___f_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14(void){
_start:
{
lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___x_256_; 
v___f_254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13);
v___f_255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___f_255_);
lean_ctor_set(v___x_256_, 1, v___f_254_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15(void){
_start:
{
lean_object* v___x_257_; lean_object* v___f_258_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14);
v___f_258_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_258_, 0, v___x_257_);
return v___f_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16(void){
_start:
{
lean_object* v___x_259_; lean_object* v___f_260_; 
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14);
v___f_260_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_260_, 0, v___x_259_);
return v___f_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17(void){
_start:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v___f_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16);
v___f_262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___f_262_);
lean_ctor_set(v___x_263_, 1, v___f_261_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18(void){
_start:
{
lean_object* v___x_264_; lean_object* v___f_265_; 
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17);
v___f_265_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_265_, 0, v___x_264_);
return v___f_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19(void){
_start:
{
lean_object* v___x_266_; lean_object* v___f_267_; 
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17);
v___f_267_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_267_, 0, v___x_266_);
return v___f_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20(void){
_start:
{
lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___x_270_; 
v___f_268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19);
v___f_269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___f_269_);
lean_ctor_set(v___x_270_, 1, v___f_268_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21(void){
_start:
{
lean_object* v___x_271_; lean_object* v___f_272_; 
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20);
v___f_272_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_272_, 0, v___x_271_);
return v___f_272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22(void){
_start:
{
lean_object* v___x_273_; lean_object* v___f_274_; 
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20);
v___f_274_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_274_, 0, v___x_273_);
return v___f_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23(void){
_start:
{
lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___x_277_; 
v___f_275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22);
v___f_276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___f_276_);
lean_ctor_set(v___x_277_, 1, v___f_275_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24(void){
_start:
{
lean_object* v___x_278_; lean_object* v___f_279_; 
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23);
v___f_279_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_279_, 0, v___x_278_);
return v___f_279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25(void){
_start:
{
lean_object* v___x_280_; lean_object* v___f_281_; 
v___x_280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_281_, 0, v___x_280_);
return v___f_281_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26(void){
_start:
{
lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v___x_284_; 
v___f_282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25);
v___f_283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___f_283_);
lean_ctor_set(v___x_284_, 1, v___f_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_292_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_291_, v___x_290_, v___x_289_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32(void){
_start:
{
lean_object* v___x_293_; lean_object* v___f_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31);
v___f_294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_296_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_295_, v___f_294_, v___x_293_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32);
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_300_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_299_, v___x_298_, v___x_297_);
return v___x_300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34(void){
_start:
{
lean_object* v___x_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___x_304_; 
v___x_301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33);
v___f_302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_304_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_303_, v___f_302_, v___x_301_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34);
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_308_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_307_, v___x_306_, v___x_305_);
return v___x_308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36(void){
_start:
{
lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___f_311_; lean_object* v___x_312_; 
v___x_309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35);
v___f_310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_312_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_311_, v___f_310_, v___x_309_);
return v___x_312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37(void){
_start:
{
lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36);
v___f_314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_316_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_315_, v___f_314_, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_320_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_319_, v___x_318_, v___x_317_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39(void){
_start:
{
lean_object* v___x_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___x_324_; 
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38);
v___f_322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_324_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_323_, v___f_322_, v___x_321_);
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___f_327_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_326_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_327_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_327_, 0, v___x_326_);
lean_closure_set(v___f_327_, 1, v___x_325_);
return v___f_327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41(void){
_start:
{
lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___f_330_; 
v___f_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_329_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_330_, 0, v___f_329_);
lean_closure_set(v___f_330_, 1, v___f_328_);
return v___f_330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42(void){
_start:
{
lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___f_333_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___f_332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_333_, 0, v___f_332_);
lean_closure_set(v___f_333_, 1, v___x_331_);
return v___f_333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43(void){
_start:
{
lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; 
v___f_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_336_, 0, v___f_335_);
lean_closure_set(v___f_336_, 1, v___f_334_);
return v___f_336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44(void){
_start:
{
lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___f_339_; 
v___f_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43);
v___f_339_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_339_, 0, v___f_338_);
lean_closure_set(v___f_339_, 1, v___f_337_);
return v___f_339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45(void){
_start:
{
lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___f_342_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___f_341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_342_, 0, v___f_341_);
lean_closure_set(v___f_342_, 1, v___x_340_);
return v___f_342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46(void){
_start:
{
lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___f_345_; 
v___f_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_345_, 0, v___f_344_);
lean_closure_set(v___f_345_, 1, v___f_343_);
return v___f_345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__47));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg(lean_object* v_x_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_toApplicative_363_; lean_object* v_toFunctor_364_; lean_object* v_toSeq_365_; lean_object* v_toSeqLeft_366_; lean_object* v_toSeqRight_367_; lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_toApplicative_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_465_; 
v___x_362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_363_ = lean_ctor_get(v___x_362_, 0);
v_toFunctor_364_ = lean_ctor_get(v_toApplicative_363_, 0);
v_toSeq_365_ = lean_ctor_get(v_toApplicative_363_, 2);
v_toSeqLeft_366_ = lean_ctor_get(v_toApplicative_363_, 3);
v_toSeqRight_367_ = lean_ctor_get(v_toApplicative_363_, 4);
v___f_368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_364_, 2);
v___f_370_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_370_, 0, v_toFunctor_364_);
v___f_371_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_371_, 0, v_toFunctor_364_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___f_370_);
lean_ctor_set(v___x_372_, 1, v___f_371_);
lean_inc(v_toSeqRight_367_);
v___f_373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_373_, 0, v_toSeqRight_367_);
lean_inc(v_toSeqLeft_366_);
v___f_374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_374_, 0, v_toSeqLeft_366_);
lean_inc(v_toSeq_365_);
v___f_375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_375_, 0, v_toSeq_365_);
v___x_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_376_, 0, v___x_372_);
lean_ctor_set(v___x_376_, 1, v___f_368_);
lean_ctor_set(v___x_376_, 2, v___f_375_);
lean_ctor_set(v___x_376_, 3, v___f_374_);
lean_ctor_set(v___x_376_, 4, v___f_373_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___f_369_);
v___x_378_ = l_StateRefT_x27_instMonad___redArg(v___x_377_);
v_toApplicative_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___x_378_, 1);
lean_dec(v_unused_466_);
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_465_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_toApplicative_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_465_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_toFunctor_383_; lean_object* v_toSeq_384_; lean_object* v_toSeqLeft_385_; lean_object* v_toSeqRight_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_463_; 
v_toFunctor_383_ = lean_ctor_get(v_toApplicative_379_, 0);
v_toSeq_384_ = lean_ctor_get(v_toApplicative_379_, 2);
v_toSeqLeft_385_ = lean_ctor_get(v_toApplicative_379_, 3);
v_toSeqRight_386_ = lean_ctor_get(v_toApplicative_379_, 4);
v_isSharedCheck_463_ = !lean_is_exclusive(v_toApplicative_379_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_dec(v_unused_464_);
v___x_388_ = v_toApplicative_379_;
v_isShared_389_ = v_isSharedCheck_463_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_toSeqRight_386_);
lean_inc(v_toSeqLeft_385_);
lean_inc(v_toSeq_384_);
lean_inc(v_toFunctor_383_);
lean_dec(v_toApplicative_379_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_463_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___f_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___f_395_; lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___x_399_; 
v___f_390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_383_);
v___f_392_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_392_, 0, v_toFunctor_383_);
v___f_393_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_393_, 0, v_toFunctor_383_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___f_392_);
lean_ctor_set(v___x_394_, 1, v___f_393_);
v___f_395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_395_, 0, v_toSeqRight_386_);
v___f_396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_396_, 0, v_toSeqLeft_385_);
v___f_397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_397_, 0, v_toSeq_384_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v___f_395_);
lean_ctor_set(v___x_388_, 3, v___f_396_);
lean_ctor_set(v___x_388_, 2, v___f_397_);
lean_ctor_set(v___x_388_, 1, v___f_390_);
lean_ctor_set(v___x_388_, 0, v___x_394_);
v___x_399_ = v___x_388_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___f_390_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v___f_397_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v___f_396_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v___f_395_);
v___x_399_ = v_reuseFailAlloc_462_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___f_391_);
lean_ctor_set(v___x_381_, 0, v___x_399_);
v___x_401_ = v___x_381_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___f_391_);
v___x_401_ = v_reuseFailAlloc_461_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_toMonadRef_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_toApplicative_416_; lean_object* v_toBind_417_; lean_object* v_getCommRing_418_; lean_object* v_modifyCommRing_419_; lean_object* v_toPure_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_1118__overap_425_; lean_object* v___x_426_; 
v___x_402_ = l_StateRefT_x27_instMonad___redArg(v___x_401_);
v___x_403_ = l_ReaderT_instMonad___redArg(v___x_402_);
v___x_404_ = l_StateRefT_x27_instMonad___redArg(v___x_403_);
v___x_405_ = l_ReaderT_instMonad___redArg(v___x_404_);
v___x_406_ = l_ReaderT_instMonad___redArg(v___x_405_);
v___x_407_ = l_StateRefT_x27_instMonad___redArg(v___x_406_);
v___x_408_ = l_ReaderT_instMonad___redArg(v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26);
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39);
v_toMonadRef_411_ = lean_ctor_get(v___x_410_, 0);
v___f_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46);
lean_inc_ref_n(v___x_408_, 2);
v___x_413_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_412_, v___x_408_);
lean_inc_ref(v_toMonadRef_411_);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v___x_409_);
lean_ctor_set(v___x_414_, 1, v_toMonadRef_411_);
lean_ctor_set(v___x_414_, 2, v___x_413_);
v___x_415_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_416_ = lean_ctor_get(v___x_408_, 0);
lean_inc_ref(v_toApplicative_416_);
v_toBind_417_ = lean_ctor_get(v___x_408_, 1);
lean_inc(v_toBind_417_);
v_getCommRing_418_ = lean_ctor_get(v___x_415_, 0);
v_modifyCommRing_419_ = lean_ctor_get(v___x_415_, 1);
v_toPure_420_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_420_);
lean_dec_ref(v_toApplicative_416_);
lean_inc(v_modifyCommRing_419_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_421_, 0, v_modifyCommRing_419_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_422_, 0, v_toPure_420_);
lean_inc(v_getCommRing_418_);
v___x_423_ = lean_apply_4(v_toBind_417_, lean_box(0), lean_box(0), v_getCommRing_418_, v___f_422_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___f_421_);
v___x_1118__overap_425_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_408_, v___x_424_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
v___x_426_ = lean_apply_12(v___x_1118__overap_425_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, lean_box(0));
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; uint8_t v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = 0;
v___x_429_ = 1;
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_431_, 0, v_a_427_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*3, v___x_428_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*3 + 1, v___x_429_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
v___x_432_ = lean_apply_8(v_x_349_, v___x_431_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, lean_box(0));
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_444_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_444_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_444_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_444_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
if (lean_obj_tag(v_a_433_) == 1)
{
lean_object* v_val_437_; lean_object* v___x_439_; 
lean_dec_ref_known(v___x_414_, 3);
lean_dec_ref(v___x_408_);
v_val_437_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_a_433_, 1);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_val_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_val_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_1121__overap_442_; lean_object* v___x_443_; 
lean_del_object(v___x_435_);
lean_dec(v_a_433_);
v___x_441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_1121__overap_442_ = l_Lean_throwError___redArg(v___x_408_, v___x_414_, v___x_441_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
v___x_443_ = lean_apply_12(v___x_1121__overap_442_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, lean_box(0));
return v___x_443_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref_known(v___x_414_, 3);
lean_dec_ref(v___x_408_);
v_a_445_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_432_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_432_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec_ref_known(v___x_414_, 3);
lean_dec_ref(v___x_408_);
lean_dec_ref(v_x_349_);
v_a_453_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_426_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_426_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___boxed(lean_object* v_x_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg(v_x_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21(lean_object* v_00_u03b1_481_, lean_object* v_x_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v_toApplicative_496_; lean_object* v_toFunctor_497_; lean_object* v_toSeq_498_; lean_object* v_toSeqLeft_499_; lean_object* v_toSeqRight_500_; lean_object* v___f_501_; lean_object* v___f_502_; lean_object* v___f_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_toApplicative_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_598_; 
v___x_495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_496_ = lean_ctor_get(v___x_495_, 0);
v_toFunctor_497_ = lean_ctor_get(v_toApplicative_496_, 0);
v_toSeq_498_ = lean_ctor_get(v_toApplicative_496_, 2);
v_toSeqLeft_499_ = lean_ctor_get(v_toApplicative_496_, 3);
v_toSeqRight_500_ = lean_ctor_get(v_toApplicative_496_, 4);
v___f_501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_497_, 2);
v___f_503_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_503_, 0, v_toFunctor_497_);
v___f_504_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_504_, 0, v_toFunctor_497_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___f_503_);
lean_ctor_set(v___x_505_, 1, v___f_504_);
lean_inc(v_toSeqRight_500_);
v___f_506_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_506_, 0, v_toSeqRight_500_);
lean_inc(v_toSeqLeft_499_);
v___f_507_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_507_, 0, v_toSeqLeft_499_);
lean_inc(v_toSeq_498_);
v___f_508_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_508_, 0, v_toSeq_498_);
v___x_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_509_, 0, v___x_505_);
lean_ctor_set(v___x_509_, 1, v___f_501_);
lean_ctor_set(v___x_509_, 2, v___f_508_);
lean_ctor_set(v___x_509_, 3, v___f_507_);
lean_ctor_set(v___x_509_, 4, v___f_506_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___f_502_);
v___x_511_ = l_StateRefT_x27_instMonad___redArg(v___x_510_);
v_toApplicative_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_511_, 1);
lean_dec(v_unused_599_);
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_598_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_toApplicative_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_598_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_toFunctor_516_; lean_object* v_toSeq_517_; lean_object* v_toSeqLeft_518_; lean_object* v_toSeqRight_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_596_; 
v_toFunctor_516_ = lean_ctor_get(v_toApplicative_512_, 0);
v_toSeq_517_ = lean_ctor_get(v_toApplicative_512_, 2);
v_toSeqLeft_518_ = lean_ctor_get(v_toApplicative_512_, 3);
v_toSeqRight_519_ = lean_ctor_get(v_toApplicative_512_, 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v_toApplicative_512_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_toApplicative_512_, 1);
lean_dec(v_unused_597_);
v___x_521_ = v_toApplicative_512_;
v_isShared_522_ = v_isSharedCheck_596_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_toSeqRight_519_);
lean_inc(v_toSeqLeft_518_);
lean_inc(v_toSeq_517_);
lean_inc(v_toFunctor_516_);
lean_dec(v_toApplicative_512_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_596_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___f_528_; lean_object* v___f_529_; lean_object* v___f_530_; lean_object* v___x_532_; 
v___f_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_516_);
v___f_525_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_525_, 0, v_toFunctor_516_);
v___f_526_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_526_, 0, v_toFunctor_516_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___f_525_);
lean_ctor_set(v___x_527_, 1, v___f_526_);
v___f_528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_528_, 0, v_toSeqRight_519_);
v___f_529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_529_, 0, v_toSeqLeft_518_);
v___f_530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_530_, 0, v_toSeq_517_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v___f_528_);
lean_ctor_set(v___x_521_, 3, v___f_529_);
lean_ctor_set(v___x_521_, 2, v___f_530_);
lean_ctor_set(v___x_521_, 1, v___f_523_);
lean_ctor_set(v___x_521_, 0, v___x_527_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___f_523_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v___f_530_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v___f_529_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___f_528_);
v___x_532_ = v_reuseFailAlloc_595_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___f_524_);
lean_ctor_set(v___x_514_, 0, v___x_532_);
v___x_534_ = v___x_514_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___f_524_);
v___x_534_ = v_reuseFailAlloc_594_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_toMonadRef_544_; lean_object* v___f_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_toApplicative_549_; lean_object* v_toBind_550_; lean_object* v_getCommRing_551_; lean_object* v_modifyCommRing_552_; lean_object* v_toPure_553_; lean_object* v___f_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_1225__overap_558_; lean_object* v___x_559_; 
v___x_535_ = l_StateRefT_x27_instMonad___redArg(v___x_534_);
v___x_536_ = l_ReaderT_instMonad___redArg(v___x_535_);
v___x_537_ = l_StateRefT_x27_instMonad___redArg(v___x_536_);
v___x_538_ = l_ReaderT_instMonad___redArg(v___x_537_);
v___x_539_ = l_ReaderT_instMonad___redArg(v___x_538_);
v___x_540_ = l_StateRefT_x27_instMonad___redArg(v___x_539_);
v___x_541_ = l_ReaderT_instMonad___redArg(v___x_540_);
v___x_542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26);
v___x_543_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39);
v_toMonadRef_544_ = lean_ctor_get(v___x_543_, 0);
v___f_545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46);
lean_inc_ref_n(v___x_541_, 2);
v___x_546_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_545_, v___x_541_);
lean_inc_ref(v_toMonadRef_544_);
v___x_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_542_);
lean_ctor_set(v___x_547_, 1, v_toMonadRef_544_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
v___x_548_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_549_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_toApplicative_549_);
v_toBind_550_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_toBind_550_);
v_getCommRing_551_ = lean_ctor_get(v___x_548_, 0);
v_modifyCommRing_552_ = lean_ctor_get(v___x_548_, 1);
v_toPure_553_ = lean_ctor_get(v_toApplicative_549_, 1);
lean_inc(v_toPure_553_);
lean_dec_ref(v_toApplicative_549_);
lean_inc(v_modifyCommRing_552_);
v___f_554_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_554_, 0, v_modifyCommRing_552_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_555_, 0, v_toPure_553_);
lean_inc(v_getCommRing_551_);
v___x_556_ = lean_apply_4(v_toBind_550_, lean_box(0), lean_box(0), v_getCommRing_551_, v___f_555_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___f_554_);
v___x_1225__overap_558_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_541_, v___x_557_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
lean_inc(v_a_491_);
lean_inc_ref(v_a_490_);
lean_inc(v_a_489_);
lean_inc_ref(v_a_488_);
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
lean_inc(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
v___x_559_ = lean_apply_12(v___x_1225__overap_558_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, lean_box(0));
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; uint8_t v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = 0;
v___x_562_ = 1;
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_564_, 0, v_a_560_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3, v___x_561_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3 + 1, v___x_562_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
lean_inc(v_a_491_);
lean_inc_ref(v_a_490_);
lean_inc(v_a_489_);
lean_inc_ref(v_a_488_);
v___x_565_ = lean_apply_8(v_x_482_, v___x_564_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, lean_box(0));
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_577_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_577_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
if (lean_obj_tag(v_a_566_) == 1)
{
lean_object* v_val_570_; lean_object* v___x_572_; 
lean_dec_ref_known(v___x_547_, 3);
lean_dec_ref(v___x_541_);
v_val_570_ = lean_ctor_get(v_a_566_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v_a_566_, 1);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v_val_570_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_val_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_1239__overap_575_; lean_object* v___x_576_; 
lean_del_object(v___x_568_);
lean_dec(v_a_566_);
v___x_574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_1239__overap_575_ = l_Lean_throwError___redArg(v___x_541_, v___x_547_, v___x_574_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
lean_inc(v_a_491_);
lean_inc_ref(v_a_490_);
lean_inc(v_a_489_);
lean_inc_ref(v_a_488_);
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
lean_inc(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
v___x_576_ = lean_apply_12(v___x_1239__overap_575_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, lean_box(0));
return v___x_576_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref_known(v___x_547_, 3);
lean_dec_ref(v___x_541_);
v_a_578_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_565_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_565_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref_known(v___x_547_, 3);
lean_dec_ref(v___x_541_);
lean_dec_ref(v_x_482_);
v_a_586_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_559_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_559_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___boxed(lean_object* v_00_u03b1_600_, lean_object* v_x_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21(v_00_u03b1_600_, v_x_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_651_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_651_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_651_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_651_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_toRing_637_; lean_object* v_charInst_x3f_638_; 
v_toRing_637_ = lean_ctor_get(v_a_628_, 0);
lean_inc_ref(v_toRing_637_);
lean_dec(v_a_628_);
v_charInst_x3f_638_ = lean_ctor_get(v_toRing_637_, 5);
lean_inc(v_charInst_x3f_638_);
lean_dec_ref(v_toRing_637_);
if (lean_obj_tag(v_charInst_x3f_638_) == 1)
{
lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
v_val_639_ = lean_ctor_get(v_charInst_x3f_638_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_charInst_x3f_638_);
if (v_isSharedCheck_650_ == 0)
{
v___x_641_ = v_charInst_x3f_638_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_dec(v_charInst_x3f_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_snd_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_snd_643_ = lean_ctor_get(v_val_639_, 1);
lean_inc(v_snd_643_);
lean_dec(v_val_639_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_nat_dec_eq(v_snd_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; 
lean_del_object(v___x_630_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_snd_643_);
v___x_647_ = v___x_641_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_snd_643_);
v___x_647_ = v_reuseFailAlloc_649_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
else
{
lean_dec(v_snd_643_);
lean_del_object(v___x_641_);
goto v___jp_632_;
}
}
}
else
{
lean_dec(v_charInst_x3f_638_);
goto v___jp_632_;
}
v___jp_632_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_635_ = v___x_630_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_627_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_627_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0___boxed(lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; uint8_t v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = 0;
v___x_689_ = 1;
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_691_, 0, v_a_687_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
lean_ctor_set(v___x_691_, 2, v___x_690_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3, v___x_688_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3 + 1, v___x_689_);
v___x_692_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_673_, v___x_691_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec_ref_known(v___x_691_, 3);
return v___x_692_;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_e_673_);
v_a_693_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_686_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_686_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(lean_object* v_msgData_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; lean_object* v_env_722_; lean_object* v___x_723_; lean_object* v_toCold_724_; lean_object* v_mctx_725_; lean_object* v_lctx_726_; lean_object* v_options_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_721_ = lean_st_ref_get(v___y_719_);
v_env_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_env_722_);
lean_dec(v___x_721_);
v___x_723_ = lean_st_ref_get(v___y_717_);
v_toCold_724_ = lean_ctor_get(v___y_718_, 0);
v_mctx_725_ = lean_ctor_get(v___x_723_, 0);
lean_inc_ref(v_mctx_725_);
lean_dec(v___x_723_);
v_lctx_726_ = lean_ctor_get(v___y_716_, 2);
v_options_727_ = lean_ctor_get(v_toCold_724_, 2);
lean_inc_ref(v_options_727_);
lean_inc_ref(v_lctx_726_);
v___x_728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_728_, 0, v_env_722_);
lean_ctor_set(v___x_728_, 1, v_mctx_725_);
lean_ctor_set(v___x_728_, 2, v_lctx_726_);
lean_ctor_set(v___x_728_, 3, v_options_727_);
v___x_729_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_msgData_715_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0___boxed(lean_object* v_msgData_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(v_msgData_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_ref_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_ref_744_ = lean_ctor_get(v___y_741_, 2);
v___x_745_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(v_msg_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
lean_inc(v_ref_744_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_ref_744_);
lean_ctor_set(v___x_750_, 1, v_a_746_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 1);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg___boxed(lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_762_, lean_object* v_k_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; uint8_t v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = 0;
v___x_779_ = 1;
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_781_, 0, v_a_777_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*3, v___x_778_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*3 + 1, v___x_779_);
v___x_782_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_763_, v_p_762_, v___x_781_);
lean_dec_ref_known(v___x_781_, 3);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_793_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_793_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
if (lean_obj_tag(v_a_783_) == 1)
{
lean_object* v_val_787_; lean_object* v___x_789_; 
v_val_787_ = lean_ctor_get(v_a_783_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v_a_783_, 1);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_val_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_val_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_del_object(v___x_785_);
lean_dec(v_a_783_);
v___x_791_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_792_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_791_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
return v___x_792_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_782_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_782_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_p_762_);
v_a_802_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_776_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_776_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_810_, lean_object* v_k_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_810_, v_k_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_k_811_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0(lean_object* v_00_u03b1_825_, lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v_msg_826_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___boxed(lean_object* v_00_u03b1_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0(v_00_u03b1_840_, v_msg_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_855_, lean_object* v_k_856_, lean_object* v_m_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; uint8_t v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = 0;
v___x_873_ = 1;
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_875_, 0, v_a_871_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*3, v___x_872_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*3 + 1, v___x_873_);
v___x_876_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_856_, v_m_857_, v_p_855_, v___x_875_);
lean_dec_ref_known(v___x_875_, 3);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_887_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_887_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_883_; 
v_val_881_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_877_, 1);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_val_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_val_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_del_object(v___x_879_);
lean_dec(v_a_877_);
v___x_885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_886_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_885_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_886_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_876_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_876_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_m_857_);
lean_dec_ref(v_p_855_);
v_a_896_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_870_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_870_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_904_, lean_object* v_k_905_, lean_object* v_m_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_904_, v_k_905_, v_m_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_k_905_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_920_, lean_object* v_p_u2082_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; uint8_t v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = 0;
v___x_937_ = 1;
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_939_, 0, v_a_935_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3, v___x_936_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 1, v___x_937_);
v___x_940_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_u2081_920_, v_p_u2082_921_, v___x_939_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec_ref_known(v___x_939_, 3);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
if (lean_obj_tag(v_a_941_) == 1)
{
lean_object* v_val_945_; lean_object* v___x_947_; 
v_val_945_ = lean_ctor_get(v_a_941_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_a_941_, 1);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_val_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_del_object(v___x_943_);
lean_dec(v_a_941_);
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_950_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_949_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_950_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_a_952_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_940_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_940_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v_p_u2082_921_);
lean_dec_ref(v_p_u2081_920_);
v_a_960_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_934_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_934_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_968_, lean_object* v_p_u2082_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_968_, v_p_u2082_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_983_, lean_object* v_p_u2082_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; uint8_t v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = 0;
v___x_1000_ = 1;
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1002_, 0, v_a_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*3, v___x_999_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*3 + 1, v___x_1000_);
v___x_1003_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_p_u2081_983_, v_p_u2082_984_, v___x_1002_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec_ref_known(v___x_1002_, 3);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1014_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
if (lean_obj_tag(v_a_1004_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v_a_1004_, 1);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_val_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_1006_);
lean_dec(v_a_1004_);
v___x_1012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_1013_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_1012_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_1013_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1003_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1003_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_p_u2082_984_);
lean_dec_ref(v_p_u2081_983_);
v_a_1023_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_997_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_997_);
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
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1031_, lean_object* v_p_u2082_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1031_, v_p_u2082_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spolM_spec__0(lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_nat_to_int(v_a_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_nat_to_int(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__1(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__2(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1054_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__1, &l_Lean_Grind_CommRing_Poly_spolM___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__1);
v___x_1055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
lean_ctor_set(v___x_1055_, 2, v___x_1052_);
lean_ctor_set(v___x_1055_, 3, v___x_1053_);
lean_ctor_set(v___x_1055_, 4, v___x_1052_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1056_, lean_object* v_p_u2082_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
if (lean_obj_tag(v_p_u2081_1056_) == 1)
{
if (lean_obj_tag(v_p_u2082_1057_) == 1)
{
lean_object* v_k_1073_; lean_object* v_v_1074_; lean_object* v_p_1075_; lean_object* v_k_1076_; lean_object* v_v_1077_; lean_object* v_p_1078_; lean_object* v_m_1079_; lean_object* v_m_u2081_1080_; lean_object* v_m_u2082_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_g_1084_; lean_object* v___x_1085_; lean_object* v_c_u2081_1086_; lean_object* v___x_1087_; lean_object* v_c_u2082_1088_; lean_object* v___x_1089_; 
v_k_1073_ = lean_ctor_get(v_p_u2081_1056_, 0);
lean_inc(v_k_1073_);
v_v_1074_ = lean_ctor_get(v_p_u2081_1056_, 1);
lean_inc_n(v_v_1074_, 2);
v_p_1075_ = lean_ctor_get(v_p_u2081_1056_, 2);
lean_inc_ref(v_p_1075_);
lean_dec_ref_known(v_p_u2081_1056_, 3);
v_k_1076_ = lean_ctor_get(v_p_u2082_1057_, 0);
lean_inc(v_k_1076_);
v_v_1077_ = lean_ctor_get(v_p_u2082_1057_, 1);
lean_inc_n(v_v_1077_, 2);
v_p_1078_ = lean_ctor_get(v_p_u2082_1057_, 2);
lean_inc_ref(v_p_1078_);
lean_dec_ref_known(v_p_u2082_1057_, 3);
v_m_1079_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1074_, v_v_1077_);
lean_inc(v_m_1079_);
v_m_u2081_1080_ = l_Lean_Grind_CommRing_Mon_div(v_m_1079_, v_v_1074_);
v_m_u2082_1081_ = l_Lean_Grind_CommRing_Mon_div(v_m_1079_, v_v_1077_);
v___x_1082_ = lean_nat_abs(v_k_1073_);
v___x_1083_ = lean_nat_abs(v_k_1076_);
v_g_1084_ = lean_nat_gcd(v___x_1082_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_nat_to_int(v_g_1084_);
v_c_u2081_1086_ = lean_int_ediv(v_k_1076_, v___x_1085_);
lean_dec(v_k_1076_);
v___x_1087_ = lean_int_neg(v_k_1073_);
lean_dec(v_k_1073_);
v_c_u2082_1088_ = lean_int_ediv(v___x_1087_, v___x_1085_);
lean_dec(v___x_1085_);
lean_dec(v___x_1087_);
lean_inc(v_m_u2081_1080_);
v___x_1089_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1075_, v_c_u2081_1086_, v_m_u2081_1080_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
lean_inc(v_m_u2082_1081_);
v___x_1091_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1078_, v_c_u2082_1088_, v_m_u2082_1081_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = l_Lean_Grind_CommRing_Poly_combineM(v_a_1090_, v_a_1092_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1094_);
lean_ctor_set(v___x_1098_, 1, v_c_u2081_1086_);
lean_ctor_set(v___x_1098_, 2, v_m_u2081_1080_);
lean_ctor_set(v___x_1098_, 3, v_c_u2082_1088_);
lean_ctor_set(v___x_1098_, 4, v_m_u2082_1081_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_c_u2082_1088_);
lean_dec(v_c_u2081_1086_);
lean_dec(v_m_u2082_1081_);
lean_dec(v_m_u2081_1080_);
v_a_1103_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1093_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1093_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_a_1090_);
lean_dec(v_c_u2082_1088_);
lean_dec(v_c_u2081_1086_);
lean_dec(v_m_u2082_1081_);
lean_dec(v_m_u2081_1080_);
v_a_1111_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1091_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1091_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_c_u2082_1088_);
lean_dec(v_c_u2081_1086_);
lean_dec(v_m_u2082_1081_);
lean_dec(v_m_u2081_1080_);
lean_dec_ref(v_p_1078_);
v_a_1119_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1089_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1089_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_dec_ref_known(v_p_u2081_1056_, 3);
lean_dec_ref(v_p_u2082_1057_);
goto v___jp_1070_;
}
}
else
{
lean_dec_ref(v_p_u2082_1057_);
lean_dec_ref(v_p_u2081_1056_);
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__2, &l_Lean_Grind_CommRing_Poly_spolM___closed__2_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__2);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1127_, lean_object* v_p_u2082_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1127_, v_p_u2082_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(lean_object* v_m_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
if (lean_obj_tag(v_m_1152_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v_p_1162_; lean_object* v_m_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_p_1162_ = lean_ctor_get(v_m_1152_, 0);
lean_inc_ref(v_p_1162_);
v_m_1163_ = lean_ctor_get(v_m_1152_, 1);
lean_inc(v_m_1163_);
lean_dec_ref_known(v_m_1152_, 2);
v___x_1164_ = l_Lean_instInhabitedExpr;
v___x_1165_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1153_, v_a_1154_, v_a_1157_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_toRingState_1167_; lean_object* v_vars_1168_; lean_object* v_x_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1236_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v_toRingState_1167_ = lean_ctor_get(v_a_1166_, 0);
lean_inc_ref(v_toRingState_1167_);
lean_dec(v_a_1166_);
v_vars_1168_ = lean_ctor_get(v_toRingState_1167_, 0);
lean_inc_ref(v_vars_1168_);
lean_dec_ref(v_toRingState_1167_);
v_x_1169_ = lean_ctor_get(v_p_1162_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_p_1162_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_p_1162_, 1);
lean_dec(v_unused_1237_);
v___x_1171_ = v_p_1162_;
v_isShared_1172_ = v_isSharedCheck_1236_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_x_1169_);
lean_dec(v_p_1162_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1236_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___y_1174_; lean_object* v_size_1232_; uint8_t v___x_1233_; 
v_size_1232_ = lean_ctor_get(v_vars_1168_, 2);
v___x_1233_ = lean_nat_dec_lt(v_x_1169_, v_size_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v_vars_1168_);
v___x_1234_ = l_outOfBounds___redArg(v___x_1164_);
v___y_1174_ = v___x_1234_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1164_, v_vars_1168_, v_x_1169_);
lean_dec_ref(v_vars_1168_);
v___y_1174_ = v___x_1235_;
goto v___jp_1173_;
}
v___jp_1173_:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = l_Lean_Expr_cleanupAnnotations(v___y_1174_);
v___x_1176_ = l_Lean_Expr_isApp(v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec_ref(v___x_1175_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v_arg_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_arg_1178_ = lean_ctor_get(v___x_1175_, 1);
lean_inc_ref(v_arg_1178_);
v___x_1179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1175_);
v___x_1180_ = l_Lean_Expr_isApp(v___x_1179_);
if (v___x_1180_ == 0)
{
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_arg_1178_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1179_);
v___x_1183_ = l_Lean_Expr_isApp(v___x_1182_);
if (v___x_1183_ == 0)
{
lean_dec_ref(v___x_1182_);
lean_dec_ref(v_arg_1178_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1182_);
v___x_1186_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2));
v___x_1187_ = l_Lean_Expr_isConstOf(v___x_1185_, v___x_1186_);
lean_dec_ref(v___x_1185_);
if (v___x_1187_ == 0)
{
lean_dec_ref(v_arg_1178_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = l_Lean_Expr_cleanupAnnotations(v_arg_1178_);
v___x_1190_ = l_Lean_Expr_isApp(v___x_1189_);
if (v___x_1190_ == 0)
{
lean_dec_ref(v___x_1189_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1189_);
v___x_1193_ = l_Lean_Expr_isApp(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_dec_ref(v___x_1192_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v_arg_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_arg_1195_ = lean_ctor_get(v___x_1192_, 1);
lean_inc_ref(v_arg_1195_);
v___x_1196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1192_);
v___x_1197_ = l_Lean_Expr_isApp(v___x_1196_);
if (v___x_1197_ == 0)
{
lean_dec_ref(v___x_1196_);
lean_dec_ref(v_arg_1195_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1196_);
v___x_1200_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5));
v___x_1201_ = l_Lean_Expr_isConstOf(v___x_1199_, v___x_1200_);
lean_dec_ref(v___x_1199_);
if (v___x_1201_ == 0)
{
lean_dec_ref(v_arg_1195_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_getNatValue_x3f(v_arg_1195_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec_ref(v_arg_1195_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1223_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1223_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1223_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
if (lean_obj_tag(v_a_1204_) == 1)
{
lean_object* v_val_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_m_1163_);
v_val_1208_ = lean_ctor_get(v_a_1204_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1210_ = v_a_1204_;
v_isShared_1211_ = v_isSharedCheck_1221_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_val_1208_);
lean_dec(v_a_1204_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1221_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v_x_1169_);
lean_ctor_set(v___x_1171_, 0, v_val_1208_);
v___x_1213_ = v___x_1171_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_val_1208_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_x_1169_);
v___x_1213_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1215_);
v___x_1217_ = v___x_1206_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
else
{
lean_del_object(v___x_1206_);
lean_dec(v_a_1204_);
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
v_m_1152_ = v_m_1163_;
goto _start;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_del_object(v___x_1171_);
lean_dec(v_x_1169_);
lean_dec(v_m_1163_);
v_a_1224_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1203_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1203_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
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
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_m_1163_);
lean_dec_ref(v_p_1162_);
v_a_1238_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1165_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1165_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___boxed(lean_object* v_m_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_m_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_m_1255_, v_a_1256_, v_a_1257_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(lean_object* v_p_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
if (lean_obj_tag(v_p_1283_) == 0)
{
lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1298_; 
v_isSharedCheck_1298_ = !lean_is_exclusive(v_p_1283_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_p_1283_, 0);
lean_dec(v_unused_1299_);
v___x_1292_ = v_p_1283_;
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_p_1283_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(0);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1294_);
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_v_1300_; lean_object* v_p_1301_; lean_object* v___x_1302_; 
v_v_1300_ = lean_ctor_get(v_p_1283_, 1);
lean_inc(v_v_1300_);
v_p_1301_ = lean_ctor_get(v_p_1283_, 2);
lean_inc_ref(v_p_1301_);
lean_dec_ref_known(v_p_1283_, 3);
v___x_1302_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_v_1300_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
if (lean_obj_tag(v_a_1303_) == 1)
{
lean_dec_ref_known(v_a_1303_, 1);
lean_dec_ref(v_p_1301_);
return v___x_1302_;
}
else
{
lean_dec(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v_p_1283_ = v_p_1301_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1301_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg___boxed(lean_object* v_p_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(v_p_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(v_p_1314_, v_a_1315_, v_a_1316_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object* v_k_u2082_x27_1342_, lean_object* v_m_u2082_1343_, lean_object* v_p_u2082_1344_, uint8_t v_checkCoeff_1345_, lean_object* v_p_u2081_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
if (lean_obj_tag(v_p_u2081_1346_) == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref_known(v_p_u2081_1346_, 1);
lean_dec_ref(v_p_u2082_1344_);
lean_dec(v_m_u2082_1343_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v_p_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1504_; 
v_k_1361_ = lean_ctor_get(v_p_u2081_1346_, 0);
v_v_1362_ = lean_ctor_get(v_p_u2081_1346_, 1);
v_p_1363_ = lean_ctor_get(v_p_u2081_1346_, 2);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_p_u2081_1346_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1365_ = v_p_u2081_1346_;
v_isShared_1366_ = v_isSharedCheck_1504_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_p_1363_);
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
lean_dec(v_p_u2081_1346_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1504_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v___y_1368_; uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_1343_, v_v_1362_);
if (v___x_1500_ == 0)
{
v___y_1368_ = v___x_1500_;
goto v___jp_1367_;
}
else
{
if (v_checkCoeff_1345_ == 0)
{
v___y_1368_ = v___x_1500_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = lean_int_emod(v_k_1361_, v_k_u2082_x27_1342_);
v___x_1502_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1503_ = lean_int_dec_eq(v___x_1501_, v___x_1502_);
lean_dec(v___x_1501_);
v___y_1368_ = v___x_1503_;
goto v___jp_1367_;
}
}
v___jp_1367_:
{
if (v___y_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1342_, v_m_u2082_1343_, v_p_u2082_1344_, v_checkCoeff_1345_, v_p_1363_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1452_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1452_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1452_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
if (lean_obj_tag(v_a_1370_) == 1)
{
lean_object* v_val_1374_; lean_object* v___x_1375_; 
lean_del_object(v___x_1372_);
v_val_1374_ = lean_ctor_get(v_a_1370_, 0);
lean_inc(v_val_1374_);
v___x_1375_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1439_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1439_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1439_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
if (lean_obj_tag(v_a_1376_) == 1)
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1412_; 
v_val_1380_ = lean_ctor_get(v_a_1376_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1376_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1382_ = v_a_1376_;
v_isShared_1383_ = v_isSharedCheck_1412_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v_a_1376_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1412_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_p_1384_; lean_object* v_k_u2081_1385_; lean_object* v_k_u2082_1386_; lean_object* v_m_u2082_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1411_; 
v_p_1384_ = lean_ctor_get(v_val_1374_, 0);
v_k_u2081_1385_ = lean_ctor_get(v_val_1374_, 1);
v_k_u2082_1386_ = lean_ctor_get(v_val_1374_, 2);
v_m_u2082_1387_ = lean_ctor_get(v_val_1374_, 3);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_val_1374_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1389_ = v_val_1374_;
v_isShared_1390_ = v_isSharedCheck_1411_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_m_u2082_1387_);
lean_inc(v_k_u2082_1386_);
lean_inc(v_k_u2081_1385_);
lean_inc(v_p_1384_);
lean_dec(v_val_1374_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1411_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1391_ = lean_int_mul(v_k_1361_, v_k_u2081_1385_);
lean_dec(v_k_1361_);
v___x_1392_ = lean_nat_to_int(v_val_1380_);
v___x_1393_ = lean_int_emod(v___x_1391_, v___x_1392_);
lean_dec(v___x_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1395_ = lean_int_dec_eq(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v_a_1370_, 1);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v_p_1384_);
lean_ctor_set(v___x_1365_, 0, v___x_1393_);
v___x_1397_ = v___x_1365_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_p_1384_);
v___x_1397_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1397_);
v___x_1399_ = v___x_1389_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_k_u2081_1385_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_k_u2082_1386_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_m_u2082_1387_);
v___x_1399_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1399_);
v___x_1401_ = v___x_1382_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1401_);
v___x_1403_ = v___x_1378_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
else
{
lean_object* v___x_1409_; 
lean_dec(v___x_1393_);
lean_del_object(v___x_1389_);
lean_dec(v_m_u2082_1387_);
lean_dec(v_k_u2082_1386_);
lean_dec(v_k_u2081_1385_);
lean_dec_ref(v_p_1384_);
lean_del_object(v___x_1382_);
lean_del_object(v___x_1365_);
lean_dec(v_v_1362_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_a_1370_);
v___x_1409_ = v___x_1378_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1370_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
else
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_a_1376_);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1370_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_a_1370_, 0);
lean_dec(v_unused_1438_);
v___x_1414_ = v_a_1370_;
v_isShared_1415_ = v_isSharedCheck_1437_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_a_1370_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1437_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_p_1416_; lean_object* v_k_u2081_1417_; lean_object* v_k_u2082_1418_; lean_object* v_m_u2082_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1436_; 
v_p_1416_ = lean_ctor_get(v_val_1374_, 0);
v_k_u2081_1417_ = lean_ctor_get(v_val_1374_, 1);
v_k_u2082_1418_ = lean_ctor_get(v_val_1374_, 2);
v_m_u2082_1419_ = lean_ctor_get(v_val_1374_, 3);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_val_1374_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1421_ = v_val_1374_;
v_isShared_1422_ = v_isSharedCheck_1436_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_m_u2082_1419_);
lean_inc(v_k_u2082_1418_);
lean_inc(v_k_u2081_1417_);
lean_inc(v_p_1416_);
lean_dec(v_val_1374_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1436_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_int_mul(v_k_1361_, v_k_u2081_1417_);
lean_dec(v_k_1361_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v_p_1416_);
lean_ctor_set(v___x_1365_, 0, v___x_1423_);
v___x_1425_ = v___x_1365_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_p_1416_);
v___x_1425_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1427_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1425_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_u2081_1417_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_k_u2082_1418_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_m_u2082_1419_);
v___x_1427_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1427_);
v___x_1429_ = v___x_1414_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1429_);
v___x_1431_ = v___x_1378_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
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
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref_known(v_a_1370_, 1);
lean_dec(v_val_1374_);
lean_del_object(v___x_1365_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
v_a_1440_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1375_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1375_);
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
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_dec(v_a_1370_);
lean_del_object(v___x_1365_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
v___x_1448_ = lean_box(0);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1448_);
v___x_1450_ = v___x_1372_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_del_object(v___x_1365_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
return v___x_1369_;
}
}
else
{
lean_object* v_m_u2082_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_g_1456_; lean_object* v___x_1457_; lean_object* v_k_u2081_1458_; lean_object* v___x_1459_; lean_object* v_k_u2082_1460_; lean_object* v___x_1461_; 
lean_del_object(v___x_1365_);
v_m_u2082_1453_ = l_Lean_Grind_CommRing_Mon_div(v_v_1362_, v_m_u2082_1343_);
v___x_1454_ = lean_nat_abs(v_k_1361_);
v___x_1455_ = lean_nat_abs(v_k_u2082_x27_1342_);
v_g_1456_ = lean_nat_gcd(v___x_1454_, v___x_1455_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_nat_to_int(v_g_1456_);
v_k_u2081_1458_ = lean_int_ediv(v_k_u2082_x27_1342_, v___x_1457_);
v___x_1459_ = lean_int_neg(v_k_1361_);
lean_dec(v_k_1361_);
v_k_u2082_1460_ = lean_int_ediv(v___x_1459_, v___x_1457_);
lean_dec(v___x_1457_);
lean_dec(v___x_1459_);
lean_inc(v_m_u2082_1453_);
v___x_1461_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_u2082_1344_, v_k_u2082_1460_, v_m_u2082_1453_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1363_, v_k_u2081_1458_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l_Lean_Grind_CommRing_Poly_combineM(v_a_1462_, v_a_1464_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1475_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1466_);
lean_ctor_set(v___x_1470_, 1, v_k_u2081_1458_);
lean_ctor_set(v___x_1470_, 2, v_k_u2082_1460_);
lean_ctor_set(v___x_1470_, 3, v_m_u2082_1453_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_k_u2082_1460_);
lean_dec(v_k_u2081_1458_);
lean_dec(v_m_u2082_1453_);
v_a_1476_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1465_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1465_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_a_1462_);
lean_dec(v_k_u2082_1460_);
lean_dec(v_k_u2081_1458_);
lean_dec(v_m_u2082_1453_);
v_a_1484_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1463_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1463_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_k_u2082_1460_);
lean_dec(v_k_u2081_1458_);
lean_dec(v_m_u2082_1453_);
lean_dec_ref(v_p_1363_);
v_a_1492_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1461_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1461_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object** _args){
lean_object* v_k_u2082_x27_1505_ = _args[0];
lean_object* v_m_u2082_1506_ = _args[1];
lean_object* v_p_u2082_1507_ = _args[2];
lean_object* v_checkCoeff_1508_ = _args[3];
lean_object* v_p_u2081_1509_ = _args[4];
lean_object* v_a_1510_ = _args[5];
lean_object* v_a_1511_ = _args[6];
lean_object* v_a_1512_ = _args[7];
lean_object* v_a_1513_ = _args[8];
lean_object* v_a_1514_ = _args[9];
lean_object* v_a_1515_ = _args[10];
lean_object* v_a_1516_ = _args[11];
lean_object* v_a_1517_ = _args[12];
lean_object* v_a_1518_ = _args[13];
lean_object* v_a_1519_ = _args[14];
lean_object* v_a_1520_ = _args[15];
lean_object* v_a_1521_ = _args[16];
_start:
{
uint8_t v_checkCoeff_boxed_1522_; lean_object* v_res_1523_; 
v_checkCoeff_boxed_1522_ = lean_unbox(v_checkCoeff_1508_);
v_res_1523_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1505_, v_m_u2082_1506_, v_p_u2082_1507_, v_checkCoeff_boxed_1522_, v_p_u2081_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_k_u2082_x27_1505_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object* v_p_u2081_1524_, lean_object* v_p_u2082_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
if (lean_obj_tag(v_p_u2082_1525_) == 1)
{
lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v_p_1540_; lean_object* v___x_1541_; 
v_k_1538_ = lean_ctor_get(v_p_u2082_1525_, 0);
lean_inc(v_k_1538_);
v_v_1539_ = lean_ctor_get(v_p_u2082_1525_, 1);
lean_inc(v_v_1539_);
v_p_1540_ = lean_ctor_get(v_p_u2082_1525_, 2);
lean_inc_ref(v_p_1540_);
lean_dec_ref_known(v_p_u2082_1525_, 3);
v___x_1541_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_1526_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1543_) == 0)
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_a_1542_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; lean_object* v___x_1546_; 
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1538_, v_v_1539_, v_p_1540_, v___x_1545_, v_p_u2081_1524_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_k_1538_);
return v___x_1546_;
}
else
{
lean_object* v_a_1547_; uint8_t v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1548_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1548_ == 0)
{
uint8_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
v___x_1550_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1538_, v_v_1539_, v_p_1540_, v___x_1549_, v_p_u2081_1524_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_k_1538_);
return v___x_1550_;
}
else
{
uint8_t v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v_a_1542_);
v___x_1551_ = 0;
v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1538_, v_v_1539_, v_p_1540_, v___x_1551_, v_p_u2081_1524_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_k_1538_);
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1542_);
lean_dec_ref(v_p_1540_);
lean_dec(v_v_1539_);
lean_dec(v_k_1538_);
lean_dec_ref(v_p_u2081_1524_);
v_a_1553_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1543_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1543_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v_p_1540_);
lean_dec(v_v_1539_);
lean_dec(v_k_1538_);
lean_dec_ref(v_p_u2081_1524_);
v_a_1561_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1541_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1541_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_p_u2082_1525_);
lean_dec_ref(v_p_u2081_1524_);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object* v_p_u2081_1571_, lean_object* v_p_u2082_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(v_p_u2081_1571_, v_p_u2082_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
return v_res_1585_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_SafePoly(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_SafePoly(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
}
#ifdef __cplusplus
}
#endif
