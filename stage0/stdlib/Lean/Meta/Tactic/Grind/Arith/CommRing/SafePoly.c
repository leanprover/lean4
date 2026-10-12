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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
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
v_toBind_70_ = lean_ctor_get(v___x_67_, 1);
v_getCommRing_71_ = lean_ctor_get(v___x_68_, 0);
v_modifyCommRing_72_ = lean_ctor_get(v___x_68_, 1);
v_toPure_73_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_modifyCommRing_72_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_74_, 0, v_modifyCommRing_72_);
lean_inc(v_toPure_73_);
v___f_75_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_75_, 0, v_toPure_73_);
lean_inc(v_toBind_70_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_8_ = stack[0].m_obj;
lean_object* v_a_9_ = stack[1].m_obj;
lean_object* v_a_10_ = stack[2].m_obj;
lean_object* v_a_11_ = stack[3].m_obj;
lean_object* v_a_12_ = stack[4].m_obj;
lean_object* v_a_13_ = stack[5].m_obj;
lean_object* v_a_14_ = stack[6].m_obj;
lean_object* v_a_15_ = stack[7].m_obj;
lean_object* v_a_16_ = stack[8].m_obj;
lean_object* v_a_17_ = stack[9].m_obj;
lean_object* v_a_18_ = stack[10].m_obj;
lean_object* v_a_19_ = stack[11].m_obj;
lean_object* v_res_100_;
v_res_100_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg(v_x_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___boxed(lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg(v_x_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_114_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly(lean_object* v_00_u03b1_115_, lean_object* v_x_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_toApplicative_130_; lean_object* v_toFunctor_131_; lean_object* v_toSeq_132_; lean_object* v_toSeqLeft_133_; lean_object* v_toSeqRight_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_toApplicative_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_206_; 
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_130_ = lean_ctor_get(v___x_129_, 0);
v_toFunctor_131_ = lean_ctor_get(v_toApplicative_130_, 0);
v_toSeq_132_ = lean_ctor_get(v_toApplicative_130_, 2);
v_toSeqLeft_133_ = lean_ctor_get(v_toApplicative_130_, 3);
v_toSeqRight_134_ = lean_ctor_get(v_toApplicative_130_, 4);
v___f_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_131_, 2);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_137_, 0, v_toFunctor_131_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_138_, 0, v_toFunctor_131_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___f_137_);
lean_ctor_set(v___x_139_, 1, v___f_138_);
lean_inc(v_toSeqRight_134_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toSeqRight_134_);
lean_inc(v_toSeqLeft_133_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_141_, 0, v_toSeqLeft_133_);
lean_inc(v_toSeq_132_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeq_132_);
v___x_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_143_, 0, v___x_139_);
lean_ctor_set(v___x_143_, 1, v___f_135_);
lean_ctor_set(v___x_143_, 2, v___f_142_);
lean_ctor_set(v___x_143_, 3, v___f_141_);
lean_ctor_set(v___x_143_, 4, v___f_140_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___f_136_);
v___x_145_ = l_StateRefT_x27_instMonad___redArg(v___x_144_);
v_toApplicative_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_145_, 1);
lean_dec(v_unused_207_);
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_206_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_toApplicative_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_206_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_toFunctor_150_; lean_object* v_toSeq_151_; lean_object* v_toSeqLeft_152_; lean_object* v_toSeqRight_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_204_; 
v_toFunctor_150_ = lean_ctor_get(v_toApplicative_146_, 0);
v_toSeq_151_ = lean_ctor_get(v_toApplicative_146_, 2);
v_toSeqLeft_152_ = lean_ctor_get(v_toApplicative_146_, 3);
v_toSeqRight_153_ = lean_ctor_get(v_toApplicative_146_, 4);
v_isSharedCheck_204_ = !lean_is_exclusive(v_toApplicative_146_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_dec(v_unused_205_);
v___x_155_ = v_toApplicative_146_;
v_isShared_156_ = v_isSharedCheck_204_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_toSeqRight_153_);
lean_inc(v_toSeqLeft_152_);
lean_inc(v_toSeq_151_);
lean_inc(v_toFunctor_150_);
lean_dec(v_toApplicative_146_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_204_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_166_; 
v___f_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_150_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_159_, 0, v_toFunctor_150_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_160_, 0, v_toFunctor_150_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___f_159_);
lean_ctor_set(v___x_161_, 1, v___f_160_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeqRight_153_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_163_, 0, v_toSeqLeft_152_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_164_, 0, v_toSeq_151_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 4, v___f_162_);
lean_ctor_set(v___x_155_, 3, v___f_163_);
lean_ctor_set(v___x_155_, 2, v___f_164_);
lean_ctor_set(v___x_155_, 1, v___f_157_);
lean_ctor_set(v___x_155_, 0, v___x_161_);
v___x_166_ = v___x_155_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___f_157_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v___f_164_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v___f_163_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v___f_162_);
v___x_166_ = v_reuseFailAlloc_203_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___f_158_);
lean_ctor_set(v___x_148_, 0, v___x_166_);
v___x_168_ = v___x_148_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___f_158_);
v___x_168_ = v_reuseFailAlloc_202_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_toApplicative_177_; lean_object* v_toBind_178_; lean_object* v_getCommRing_179_; lean_object* v_modifyCommRing_180_; lean_object* v_toPure_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_753__overap_186_; lean_object* v___x_187_; 
v___x_169_ = l_StateRefT_x27_instMonad___redArg(v___x_168_);
v___x_170_ = l_ReaderT_instMonad___redArg(v___x_169_);
v___x_171_ = l_StateRefT_x27_instMonad___redArg(v___x_170_);
v___x_172_ = l_ReaderT_instMonad___redArg(v___x_171_);
v___x_173_ = l_ReaderT_instMonad___redArg(v___x_172_);
v___x_174_ = l_StateRefT_x27_instMonad___redArg(v___x_173_);
v___x_175_ = l_ReaderT_instMonad___redArg(v___x_174_);
v___x_176_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_177_ = lean_ctor_get(v___x_175_, 0);
v_toBind_178_ = lean_ctor_get(v___x_175_, 1);
v_getCommRing_179_ = lean_ctor_get(v___x_176_, 0);
v_modifyCommRing_180_ = lean_ctor_get(v___x_176_, 1);
v_toPure_181_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_inc(v_modifyCommRing_180_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_182_, 0, v_modifyCommRing_180_);
lean_inc(v_toPure_181_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_183_, 0, v_toPure_181_);
lean_inc(v_toBind_178_);
lean_inc(v_getCommRing_179_);
v___x_184_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v_getCommRing_179_, v___f_183_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___f_182_);
v___x_753__overap_186_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_175_, v___x_185_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v_a_120_);
lean_inc(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
v___x_187_ = lean_apply_12(v___x_753__overap_186_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; uint8_t v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
v___x_189_ = 0;
v___x_190_ = 1;
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_192_, 0, v_a_188_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_ctor_set(v___x_192_, 2, v___x_191_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*3, v___x_189_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*3 + 1, v___x_190_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
v___x_193_ = lean_apply_8(v_x_116_, v___x_192_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
return v___x_193_;
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v_x_116_);
v_a_194_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_187_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_187_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_116_ = stack[1].m_obj;
lean_object* v_a_117_ = stack[2].m_obj;
lean_object* v_a_118_ = stack[3].m_obj;
lean_object* v_a_119_ = stack[4].m_obj;
lean_object* v_a_120_ = stack[5].m_obj;
lean_object* v_a_121_ = stack[6].m_obj;
lean_object* v_a_122_ = stack[7].m_obj;
lean_object* v_a_123_ = stack[8].m_obj;
lean_object* v_a_124_ = stack[9].m_obj;
lean_object* v_a_125_ = stack[10].m_obj;
lean_object* v_a_126_ = stack[11].m_obj;
lean_object* v_a_127_ = stack[12].m_obj;
lean_object* v_res_208_;
v_res_208_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly(lean_box(0), v_x_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___boxed(lean_object* v_00_u03b1_209_, lean_object* v_x_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly(v_00_u03b1_209_, v_x_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0(void){
_start:
{
lean_object* v___x_224_; lean_object* v___f_225_; 
v___x_224_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_225_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_225_, 0, v___x_224_);
return v___f_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___f_227_; 
v___x_226_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_227_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_227_, 0, v___x_226_);
return v___f_227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2(void){
_start:
{
lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___x_230_; 
v___f_228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__1);
v___f_229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__0);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___f_229_);
lean_ctor_set(v___x_230_, 1, v___f_228_);
return v___x_230_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___f_232_; 
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_232_, 0, v___x_231_);
return v___f_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4(void){
_start:
{
lean_object* v___x_233_; lean_object* v___f_234_; 
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__2);
v___f_234_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_234_, 0, v___x_233_);
return v___f_234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5(void){
_start:
{
lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___x_237_; 
v___f_235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__4);
v___f_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__3);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___f_236_);
lean_ctor_set(v___x_237_, 1, v___f_235_);
return v___x_237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6(void){
_start:
{
lean_object* v___x_238_; lean_object* v___f_239_; 
v___x_238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5);
v___f_239_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_239_, 0, v___x_238_);
return v___f_239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7(void){
_start:
{
lean_object* v___x_240_; lean_object* v___f_241_; 
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__5);
v___f_241_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_241_, 0, v___x_240_);
return v___f_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8(void){
_start:
{
lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___x_244_; 
v___f_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__7);
v___f_243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__6);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___f_243_);
lean_ctor_set(v___x_244_, 1, v___f_242_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9(void){
_start:
{
lean_object* v___x_245_; lean_object* v___f_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8);
v___f_246_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_246_, 0, v___x_245_);
return v___f_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10(void){
_start:
{
lean_object* v___x_247_; lean_object* v___f_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__8);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_248_, 0, v___x_247_);
return v___f_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11(void){
_start:
{
lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_251_; 
v___f_249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__10);
v___f_250_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__9);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___f_250_);
lean_ctor_set(v___x_251_, 1, v___f_249_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12(void){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; 
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11);
v___f_253_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
return v___f_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13(void){
_start:
{
lean_object* v___x_254_; lean_object* v___f_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__11);
v___f_255_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_255_, 0, v___x_254_);
return v___f_255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14(void){
_start:
{
lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___x_258_; 
v___f_256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__13);
v___f_257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__12);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___f_257_);
lean_ctor_set(v___x_258_, 1, v___f_256_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15(void){
_start:
{
lean_object* v___x_259_; lean_object* v___f_260_; 
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14);
v___f_260_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_260_, 0, v___x_259_);
return v___f_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16(void){
_start:
{
lean_object* v___x_261_; lean_object* v___f_262_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__14);
v___f_262_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_262_, 0, v___x_261_);
return v___f_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17(void){
_start:
{
lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___x_265_; 
v___f_263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__16);
v___f_264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__15);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___f_264_);
lean_ctor_set(v___x_265_, 1, v___f_263_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18(void){
_start:
{
lean_object* v___x_266_; lean_object* v___f_267_; 
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17);
v___f_267_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_267_, 0, v___x_266_);
return v___f_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19(void){
_start:
{
lean_object* v___x_268_; lean_object* v___f_269_; 
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__17);
v___f_269_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_269_, 0, v___x_268_);
return v___f_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20(void){
_start:
{
lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___x_272_; 
v___f_270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__19);
v___f_271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__18);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___f_271_);
lean_ctor_set(v___x_272_, 1, v___f_270_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21(void){
_start:
{
lean_object* v___x_273_; lean_object* v___f_274_; 
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20);
v___f_274_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_274_, 0, v___x_273_);
return v___f_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22(void){
_start:
{
lean_object* v___x_275_; lean_object* v___f_276_; 
v___x_275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__20);
v___f_276_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_276_, 0, v___x_275_);
return v___f_276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23(void){
_start:
{
lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___x_279_; 
v___f_277_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__22);
v___f_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__21);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___f_278_);
lean_ctor_set(v___x_279_, 1, v___f_277_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24(void){
_start:
{
lean_object* v___x_280_; lean_object* v___f_281_; 
v___x_280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_281_, 0, v___x_280_);
return v___f_281_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25(void){
_start:
{
lean_object* v___x_282_; lean_object* v___f_283_; 
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__23);
v___f_283_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_283_, 0, v___x_282_);
return v___f_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26(void){
_start:
{
lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___x_286_; 
v___f_284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__25);
v___f_285_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__24);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___f_285_);
lean_ctor_set(v___x_286_, 1, v___f_284_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_294_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_293_, v___x_292_, v___x_291_);
return v___x_294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32(void){
_start:
{
lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___x_298_; 
v___x_295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__31);
v___f_296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_298_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_297_, v___f_296_, v___x_295_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__32);
v___x_300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_302_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_301_, v___x_300_, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34(void){
_start:
{
lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___x_306_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__33);
v___f_304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_306_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_305_, v___f_304_, v___x_303_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__34);
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_310_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_309_, v___x_308_, v___x_307_);
return v___x_310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36(void){
_start:
{
lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___x_314_; 
v___x_311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__35);
v___f_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_314_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_313_, v___f_312_, v___x_311_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37(void){
_start:
{
lean_object* v___x_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__36);
v___f_316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_318_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_317_, v___f_316_, v___x_315_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__37);
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__29));
v___x_322_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_321_, v___x_320_, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39(void){
_start:
{
lean_object* v___x_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__38);
v___f_324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__27));
v___x_326_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_325_, v___f_324_, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___f_329_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___x_328_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_329_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_329_, 0, v___x_328_);
lean_closure_set(v___f_329_, 1, v___x_327_);
return v___f_329_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41(void){
_start:
{
lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___f_332_; 
v___f_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__40);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_332_, 0, v___f_331_);
lean_closure_set(v___f_332_, 1, v___f_330_);
return v___f_332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42(void){
_start:
{
lean_object* v___x_333_; lean_object* v___f_334_; lean_object* v___f_335_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___f_334_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__41);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_335_, 0, v___f_334_);
lean_closure_set(v___f_335_, 1, v___x_333_);
return v___f_335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43(void){
_start:
{
lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___f_338_; 
v___f_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__42);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_338_, 0, v___f_337_);
lean_closure_set(v___f_338_, 1, v___f_336_);
return v___f_338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44(void){
_start:
{
lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___f_341_; 
v___f_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__43);
v___f_341_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_341_, 0, v___f_340_);
lean_closure_set(v___f_341_, 1, v___f_339_);
return v___f_341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45(void){
_start:
{
lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___f_344_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__30));
v___f_343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__44);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_344_, 0, v___f_343_);
lean_closure_set(v___f_344_, 1, v___x_342_);
return v___f_344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46(void){
_start:
{
lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___f_347_; 
v___f_345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__28));
v___f_346_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__45);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_347_, 0, v___f_346_);
lean_closure_set(v___f_347_, 1, v___f_345_);
return v___f_347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__47));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg(lean_object* v_x_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_toApplicative_365_; lean_object* v_toFunctor_366_; lean_object* v_toSeq_367_; lean_object* v_toSeqLeft_368_; lean_object* v_toSeqRight_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_toApplicative_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_467_; 
v___x_364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_365_ = lean_ctor_get(v___x_364_, 0);
v_toFunctor_366_ = lean_ctor_get(v_toApplicative_365_, 0);
v_toSeq_367_ = lean_ctor_get(v_toApplicative_365_, 2);
v_toSeqLeft_368_ = lean_ctor_get(v_toApplicative_365_, 3);
v_toSeqRight_369_ = lean_ctor_get(v_toApplicative_365_, 4);
v___f_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_366_, 2);
v___f_372_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_372_, 0, v_toFunctor_366_);
v___f_373_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_373_, 0, v_toFunctor_366_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___f_372_);
lean_ctor_set(v___x_374_, 1, v___f_373_);
lean_inc(v_toSeqRight_369_);
v___f_375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_375_, 0, v_toSeqRight_369_);
lean_inc(v_toSeqLeft_368_);
v___f_376_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_376_, 0, v_toSeqLeft_368_);
lean_inc(v_toSeq_367_);
v___f_377_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_377_, 0, v_toSeq_367_);
v___x_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_378_, 0, v___x_374_);
lean_ctor_set(v___x_378_, 1, v___f_370_);
lean_ctor_set(v___x_378_, 2, v___f_377_);
lean_ctor_set(v___x_378_, 3, v___f_376_);
lean_ctor_set(v___x_378_, 4, v___f_375_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___f_371_);
v___x_380_ = l_StateRefT_x27_instMonad___redArg(v___x_379_);
v_toApplicative_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_380_, 1);
lean_dec(v_unused_468_);
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_467_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_toApplicative_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_467_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_toFunctor_385_; lean_object* v_toSeq_386_; lean_object* v_toSeqLeft_387_; lean_object* v_toSeqRight_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_465_; 
v_toFunctor_385_ = lean_ctor_get(v_toApplicative_381_, 0);
v_toSeq_386_ = lean_ctor_get(v_toApplicative_381_, 2);
v_toSeqLeft_387_ = lean_ctor_get(v_toApplicative_381_, 3);
v_toSeqRight_388_ = lean_ctor_get(v_toApplicative_381_, 4);
v_isSharedCheck_465_ = !lean_is_exclusive(v_toApplicative_381_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_toApplicative_381_, 1);
lean_dec(v_unused_466_);
v___x_390_ = v_toApplicative_381_;
v_isShared_391_ = v_isSharedCheck_465_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_toSeqRight_388_);
lean_inc(v_toSeqLeft_387_);
lean_inc(v_toSeq_386_);
lean_inc(v_toFunctor_385_);
lean_dec(v_toApplicative_381_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_465_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___f_392_; lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___f_397_; lean_object* v___f_398_; lean_object* v___f_399_; lean_object* v___x_401_; 
v___f_392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_385_);
v___f_394_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_394_, 0, v_toFunctor_385_);
v___f_395_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_395_, 0, v_toFunctor_385_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___f_394_);
lean_ctor_set(v___x_396_, 1, v___f_395_);
v___f_397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_397_, 0, v_toSeqRight_388_);
v___f_398_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_398_, 0, v_toSeqLeft_387_);
v___f_399_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_399_, 0, v_toSeq_386_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 4, v___f_397_);
lean_ctor_set(v___x_390_, 3, v___f_398_);
lean_ctor_set(v___x_390_, 2, v___f_399_);
lean_ctor_set(v___x_390_, 1, v___f_392_);
lean_ctor_set(v___x_390_, 0, v___x_396_);
v___x_401_ = v___x_390_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___f_392_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___f_399_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v___f_398_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v___f_397_);
v___x_401_ = v_reuseFailAlloc_464_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___f_393_);
lean_ctor_set(v___x_383_, 0, v___x_401_);
v___x_403_ = v___x_383_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___f_393_);
v___x_403_ = v_reuseFailAlloc_463_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_toMonadRef_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_toApplicative_418_; lean_object* v_toBind_419_; lean_object* v_getCommRing_420_; lean_object* v_modifyCommRing_421_; lean_object* v_toPure_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_1118__overap_427_; lean_object* v___x_428_; 
v___x_404_ = l_StateRefT_x27_instMonad___redArg(v___x_403_);
v___x_405_ = l_ReaderT_instMonad___redArg(v___x_404_);
v___x_406_ = l_StateRefT_x27_instMonad___redArg(v___x_405_);
v___x_407_ = l_ReaderT_instMonad___redArg(v___x_406_);
v___x_408_ = l_ReaderT_instMonad___redArg(v___x_407_);
v___x_409_ = l_StateRefT_x27_instMonad___redArg(v___x_408_);
v___x_410_ = l_ReaderT_instMonad___redArg(v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26);
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39);
v_toMonadRef_413_ = lean_ctor_get(v___x_412_, 0);
v___f_414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46);
lean_inc_ref_n(v___x_410_, 2);
v___x_415_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_414_, v___x_410_);
lean_inc_ref(v_toMonadRef_413_);
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_411_);
lean_ctor_set(v___x_416_, 1, v_toMonadRef_413_);
lean_ctor_set(v___x_416_, 2, v___x_415_);
v___x_417_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_418_ = lean_ctor_get(v___x_410_, 0);
v_toBind_419_ = lean_ctor_get(v___x_410_, 1);
v_getCommRing_420_ = lean_ctor_get(v___x_417_, 0);
v_modifyCommRing_421_ = lean_ctor_get(v___x_417_, 1);
v_toPure_422_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_modifyCommRing_421_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_423_, 0, v_modifyCommRing_421_);
lean_inc(v_toPure_422_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_424_, 0, v_toPure_422_);
lean_inc(v_toBind_419_);
lean_inc(v_getCommRing_420_);
v___x_425_ = lean_apply_4(v_toBind_419_, lean_box(0), lean_box(0), v_getCommRing_420_, v___f_424_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___f_423_);
v___x_1118__overap_427_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_410_, v___x_426_);
lean_inc(v_a_362_);
lean_inc_ref(v_a_361_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
v___x_428_ = lean_apply_12(v___x_1118__overap_427_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, lean_box(0));
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; uint8_t v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = 0;
v___x_431_ = 1;
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_433_, 0, v_a_429_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*3, v___x_430_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*3 + 1, v___x_431_);
lean_inc(v_a_362_);
lean_inc_ref(v_a_361_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
v___x_434_ = lean_apply_8(v_x_351_, v___x_433_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, lean_box(0));
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_446_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_446_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_446_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_446_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
if (lean_obj_tag(v_a_435_) == 1)
{
lean_object* v_val_439_; lean_object* v___x_441_; 
lean_dec_ref_known(v___x_416_, 3);
lean_dec_ref(v___x_410_);
v_val_439_ = lean_ctor_get(v_a_435_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_a_435_, 1);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_val_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_val_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_1121__overap_444_; lean_object* v___x_445_; 
lean_del_object(v___x_437_);
lean_dec(v_a_435_);
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_1121__overap_444_ = l_Lean_throwError___redArg(v___x_410_, v___x_416_, v___x_443_);
lean_inc(v_a_362_);
lean_inc_ref(v_a_361_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
v___x_445_ = lean_apply_12(v___x_1121__overap_444_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, lean_box(0));
return v___x_445_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref_known(v___x_416_, 3);
lean_dec_ref(v___x_410_);
v_a_447_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_434_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_434_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref_known(v___x_416_, 3);
lean_dec_ref(v___x_410_);
lean_dec_ref(v_x_351_);
v_a_455_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_428_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_428_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_351_ = stack[0].m_obj;
lean_object* v_a_352_ = stack[1].m_obj;
lean_object* v_a_353_ = stack[2].m_obj;
lean_object* v_a_354_ = stack[3].m_obj;
lean_object* v_a_355_ = stack[4].m_obj;
lean_object* v_a_356_ = stack[5].m_obj;
lean_object* v_a_357_ = stack[6].m_obj;
lean_object* v_a_358_ = stack[7].m_obj;
lean_object* v_a_359_ = stack[8].m_obj;
lean_object* v_a_360_ = stack[9].m_obj;
lean_object* v_a_361_ = stack[10].m_obj;
lean_object* v_a_362_ = stack[11].m_obj;
lean_object* v_res_469_;
v_res_469_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg(v_x_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___boxed(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg(v_x_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_483_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21(lean_object* v_00_u03b1_484_, lean_object* v_x_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_toApplicative_499_; lean_object* v_toFunctor_500_; lean_object* v_toSeq_501_; lean_object* v_toSeqLeft_502_; lean_object* v_toSeqRight_503_; lean_object* v___f_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___f_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_toApplicative_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_601_; 
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__1);
v_toApplicative_499_ = lean_ctor_get(v___x_498_, 0);
v_toFunctor_500_ = lean_ctor_get(v_toApplicative_499_, 0);
v_toSeq_501_ = lean_ctor_get(v_toApplicative_499_, 2);
v_toSeqLeft_502_ = lean_ctor_get(v_toApplicative_499_, 3);
v_toSeqRight_503_ = lean_ctor_get(v_toApplicative_499_, 4);
v___f_504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__2));
v___f_505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_500_, 2);
v___f_506_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_506_, 0, v_toFunctor_500_);
v___f_507_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_507_, 0, v_toFunctor_500_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___f_506_);
lean_ctor_set(v___x_508_, 1, v___f_507_);
lean_inc(v_toSeqRight_503_);
v___f_509_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_509_, 0, v_toSeqRight_503_);
lean_inc(v_toSeqLeft_502_);
v___f_510_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_510_, 0, v_toSeqLeft_502_);
lean_inc(v_toSeq_501_);
v___f_511_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_511_, 0, v_toSeq_501_);
v___x_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_512_, 0, v___x_508_);
lean_ctor_set(v___x_512_, 1, v___f_504_);
lean_ctor_set(v___x_512_, 2, v___f_511_);
lean_ctor_set(v___x_512_, 3, v___f_510_);
lean_ctor_set(v___x_512_, 4, v___f_509_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___f_505_);
v___x_514_ = l_StateRefT_x27_instMonad___redArg(v___x_513_);
v_toApplicative_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_514_, 1);
lean_dec(v_unused_602_);
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_601_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_toApplicative_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_601_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_toFunctor_519_; lean_object* v_toSeq_520_; lean_object* v_toSeqLeft_521_; lean_object* v_toSeqRight_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_599_; 
v_toFunctor_519_ = lean_ctor_get(v_toApplicative_515_, 0);
v_toSeq_520_ = lean_ctor_get(v_toApplicative_515_, 2);
v_toSeqLeft_521_ = lean_ctor_get(v_toApplicative_515_, 3);
v_toSeqRight_522_ = lean_ctor_get(v_toApplicative_515_, 4);
v_isSharedCheck_599_ = !lean_is_exclusive(v_toApplicative_515_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_toApplicative_515_, 1);
lean_dec(v_unused_600_);
v___x_524_ = v_toApplicative_515_;
v_isShared_525_ = v_isSharedCheck_599_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_toSeqRight_522_);
lean_inc(v_toSeqLeft_521_);
lean_inc(v_toSeq_520_);
lean_inc(v_toFunctor_519_);
lean_dec(v_toApplicative_515_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_599_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___f_528_; lean_object* v___f_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___x_535_; 
v___f_526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__4));
v___f_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly___redArg___closed__5));
lean_inc_ref(v_toFunctor_519_);
v___f_528_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_528_, 0, v_toFunctor_519_);
v___f_529_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_529_, 0, v_toFunctor_519_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___f_528_);
lean_ctor_set(v___x_530_, 1, v___f_529_);
v___f_531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_531_, 0, v_toSeqRight_522_);
v___f_532_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_532_, 0, v_toSeqLeft_521_);
v___f_533_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_533_, 0, v_toSeq_520_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v___f_531_);
lean_ctor_set(v___x_524_, 3, v___f_532_);
lean_ctor_set(v___x_524_, 2, v___f_533_);
lean_ctor_set(v___x_524_, 1, v___f_526_);
lean_ctor_set(v___x_524_, 0, v___x_530_);
v___x_535_ = v___x_524_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___f_526_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v___f_533_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___f_532_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v___f_531_);
v___x_535_ = v_reuseFailAlloc_598_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v___f_527_);
lean_ctor_set(v___x_517_, 0, v___x_535_);
v___x_537_ = v___x_517_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___f_527_);
v___x_537_ = v_reuseFailAlloc_597_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_toMonadRef_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_toApplicative_552_; lean_object* v_toBind_553_; lean_object* v_getCommRing_554_; lean_object* v_modifyCommRing_555_; lean_object* v_toPure_556_; lean_object* v___f_557_; lean_object* v___f_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_1225__overap_561_; lean_object* v___x_562_; 
v___x_538_ = l_StateRefT_x27_instMonad___redArg(v___x_537_);
v___x_539_ = l_ReaderT_instMonad___redArg(v___x_538_);
v___x_540_ = l_StateRefT_x27_instMonad___redArg(v___x_539_);
v___x_541_ = l_ReaderT_instMonad___redArg(v___x_540_);
v___x_542_ = l_ReaderT_instMonad___redArg(v___x_541_);
v___x_543_ = l_StateRefT_x27_instMonad___redArg(v___x_542_);
v___x_544_ = l_ReaderT_instMonad___redArg(v___x_543_);
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__26);
v___x_546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__39);
v_toMonadRef_547_ = lean_ctor_get(v___x_546_, 0);
v___f_548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__46);
lean_inc_ref_n(v___x_544_, 2);
v___x_549_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_548_, v___x_544_);
lean_inc_ref(v_toMonadRef_547_);
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v___x_545_);
lean_ctor_set(v___x_550_, 1, v_toMonadRef_547_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
v___x_551_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
v_toApplicative_552_ = lean_ctor_get(v___x_544_, 0);
v_toBind_553_ = lean_ctor_get(v___x_544_, 1);
v_getCommRing_554_ = lean_ctor_get(v___x_551_, 0);
v_modifyCommRing_555_ = lean_ctor_get(v___x_551_, 1);
v_toPure_556_ = lean_ctor_get(v_toApplicative_552_, 1);
lean_inc(v_modifyCommRing_555_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_557_, 0, v_modifyCommRing_555_);
lean_inc(v_toPure_556_);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_558_, 0, v_toPure_556_);
lean_inc(v_toBind_553_);
lean_inc(v_getCommRing_554_);
v___x_559_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v_getCommRing_554_, v___f_558_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___f_557_);
v___x_1225__overap_561_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v___x_544_, v___x_560_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc(v_a_492_);
lean_inc_ref(v_a_491_);
lean_inc(v_a_490_);
lean_inc_ref(v_a_489_);
lean_inc(v_a_488_);
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
v___x_562_ = lean_apply_12(v___x_1225__overap_561_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, lean_box(0));
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; uint8_t v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = 0;
v___x_565_ = 1;
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_567_, 0, v_a_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
lean_ctor_set(v___x_567_, 2, v___x_566_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3, v___x_564_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3 + 1, v___x_565_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc(v_a_492_);
lean_inc_ref(v_a_491_);
v___x_568_ = lean_apply_8(v_x_485_, v___x_567_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, lean_box(0));
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_580_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_580_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_580_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_580_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_575_; 
lean_dec_ref_known(v___x_550_, 3);
lean_dec_ref(v___x_544_);
v_val_573_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_a_569_, 1);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_val_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_val_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_1239__overap_578_; lean_object* v___x_579_; 
lean_del_object(v___x_571_);
lean_dec(v_a_569_);
v___x_577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_1239__overap_578_ = l_Lean_throwError___redArg(v___x_544_, v___x_550_, v___x_577_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc(v_a_492_);
lean_inc_ref(v_a_491_);
lean_inc(v_a_490_);
lean_inc_ref(v_a_489_);
lean_inc(v_a_488_);
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
v___x_579_ = lean_apply_12(v___x_1239__overap_578_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, lean_box(0));
return v___x_579_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref_known(v___x_550_, 3);
lean_dec_ref(v___x_544_);
v_a_581_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_568_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_568_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref_known(v___x_550_, 3);
lean_dec_ref(v___x_544_);
lean_dec_ref(v_x_485_);
v_a_589_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_562_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_562_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_485_ = stack[1].m_obj;
lean_object* v_a_486_ = stack[2].m_obj;
lean_object* v_a_487_ = stack[3].m_obj;
lean_object* v_a_488_ = stack[4].m_obj;
lean_object* v_a_489_ = stack[5].m_obj;
lean_object* v_a_490_ = stack[6].m_obj;
lean_object* v_a_491_ = stack[7].m_obj;
lean_object* v_a_492_ = stack[8].m_obj;
lean_object* v_a_493_ = stack[9].m_obj;
lean_object* v_a_494_ = stack[10].m_obj;
lean_object* v_a_495_ = stack[11].m_obj;
lean_object* v_a_496_ = stack[12].m_obj;
lean_object* v_res_603_;
v_res_603_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21(lean_box(0), v_x_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___boxed(lean_object* v_00_u03b1_604_, lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21(v_00_u03b1_604_, v_x_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_618_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_655_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_655_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_655_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_655_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_toRing_641_; lean_object* v_charInst_x3f_642_; 
v_toRing_641_ = lean_ctor_get(v_a_632_, 0);
lean_inc_ref(v_toRing_641_);
lean_dec(v_a_632_);
v_charInst_x3f_642_ = lean_ctor_get(v_toRing_641_, 5);
lean_inc(v_charInst_x3f_642_);
lean_dec_ref(v_toRing_641_);
if (lean_obj_tag(v_charInst_x3f_642_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_val_643_ = lean_ctor_get(v_charInst_x3f_642_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_charInst_x3f_642_);
if (v_isSharedCheck_654_ == 0)
{
v___x_645_ = v_charInst_x3f_642_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v_charInst_x3f_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_snd_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_snd_647_ = lean_ctor_get(v_val_643_, 1);
lean_inc(v_snd_647_);
lean_dec(v_val_643_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_nat_dec_eq(v_snd_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_651_; 
lean_del_object(v___x_634_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_snd_647_);
v___x_651_ = v___x_645_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_snd_647_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
else
{
lean_dec(v_snd_647_);
lean_del_object(v___x_645_);
goto v___jp_636_;
}
}
}
else
{
lean_dec(v_charInst_x3f_642_);
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_box(0);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_631_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_631_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_619_ = stack[0].m_obj;
lean_object* v___y_620_ = stack[1].m_obj;
lean_object* v___y_621_ = stack[2].m_obj;
lean_object* v___y_622_ = stack[3].m_obj;
lean_object* v___y_623_ = stack[4].m_obj;
lean_object* v___y_624_ = stack[5].m_obj;
lean_object* v___y_625_ = stack[6].m_obj;
lean_object* v___y_626_ = stack[7].m_obj;
lean_object* v___y_627_ = stack[8].m_obj;
lean_object* v___y_628_ = stack[9].m_obj;
lean_object* v___y_629_ = stack[10].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0___boxed(lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_677_;
}
}
lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; uint8_t v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = 0;
v___x_694_ = 1;
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_696_, 0, v_a_692_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*3, v___x_693_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*3 + 1, v___x_694_);
v___x_697_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_678_, v___x_696_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref_known(v___x_696_, 3);
return v___x_697_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_e_678_);
v_a_698_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_691_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_691_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Expr_toPolyM_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_678_ = stack[0].m_obj;
lean_object* v_a_679_ = stack[1].m_obj;
lean_object* v_a_680_ = stack[2].m_obj;
lean_object* v_a_681_ = stack[3].m_obj;
lean_object* v_a_682_ = stack[4].m_obj;
lean_object* v_a_683_ = stack[5].m_obj;
lean_object* v_a_684_ = stack[6].m_obj;
lean_object* v_a_685_ = stack[7].m_obj;
lean_object* v_a_686_ = stack[8].m_obj;
lean_object* v_a_687_ = stack[9].m_obj;
lean_object* v_a_688_ = stack[10].m_obj;
lean_object* v_a_689_ = stack[11].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_720_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(lean_object* v_msgData_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; lean_object* v_env_728_; uint8_t v___x_729_; lean_object* v_env_730_; lean_object* v___x_731_; lean_object* v_toCold_732_; lean_object* v_mctx_733_; lean_object* v_lctx_734_; lean_object* v_options_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_727_ = lean_st_ref_get(v___y_725_);
v_env_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_ref(v_env_728_);
lean_dec(v___x_727_);
v___x_729_ = 0;
v_env_730_ = l_Lean_Environment_setRecordingDeps(v_env_728_, v___x_729_);
v___x_731_ = lean_st_ref_get(v___y_723_);
v_toCold_732_ = lean_ctor_get(v___y_724_, 0);
v_mctx_733_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_mctx_733_);
lean_dec(v___x_731_);
v_lctx_734_ = lean_ctor_get(v___y_722_, 2);
v_options_735_ = lean_ctor_get(v_toCold_732_, 2);
lean_inc_ref(v_options_735_);
lean_inc_ref(v_lctx_734_);
v___x_736_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_736_, 0, v_env_730_);
lean_ctor_set(v___x_736_, 1, v_mctx_733_);
lean_ctor_set(v___x_736_, 2, v_lctx_734_);
lean_ctor_set(v___x_736_, 3, v_options_735_);
v___x_737_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v_msgData_721_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_721_ = stack[0].m_obj;
lean_object* v___y_722_ = stack[1].m_obj;
lean_object* v___y_723_ = stack[2].m_obj;
lean_object* v___y_724_ = stack[3].m_obj;
lean_object* v___y_725_ = stack[4].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(v_msgData_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0___boxed(lean_object* v_msgData_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(v_msgData_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_ref_753_; lean_object* v___x_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_ref_753_ = lean_ctor_get(v___y_750_, 2);
v___x_754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_spec__0(v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_inc(v_ref_753_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_ref_753_);
lean_ctor_set(v___x_759_, 1, v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 1);
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_747_ = stack[0].m_obj;
lean_object* v___y_748_ = stack[1].m_obj;
lean_object* v___y_749_ = stack[2].m_obj;
lean_object* v___y_750_ = stack[3].m_obj;
lean_object* v___y_751_ = stack[4].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg___boxed(lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v_msg_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_772_, lean_object* v_k_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; uint8_t v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = 0;
v___x_789_ = 1;
v___x_790_ = lean_box(0);
v___x_791_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_791_, 0, v_a_787_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*3, v___x_788_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*3 + 1, v___x_789_);
v___x_792_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_773_, v_p_772_, v___x_791_);
lean_dec_ref_known(v___x_791_, 3);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
if (lean_obj_tag(v_a_793_) == 1)
{
lean_object* v_val_797_; lean_object* v___x_799_; 
v_val_797_ = lean_ctor_get(v_a_793_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v_a_793_, 1);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_val_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_del_object(v___x_795_);
lean_dec(v_a_793_);
v___x_801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_802_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_801_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_802_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_a_804_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_792_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_792_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_p_772_);
v_a_812_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_786_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_786_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_mulConstM_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_772_ = stack[0].m_obj;
lean_object* v_k_773_ = stack[1].m_obj;
lean_object* v_a_774_ = stack[2].m_obj;
lean_object* v_a_775_ = stack[3].m_obj;
lean_object* v_a_776_ = stack[4].m_obj;
lean_object* v_a_777_ = stack[5].m_obj;
lean_object* v_a_778_ = stack[6].m_obj;
lean_object* v_a_779_ = stack[7].m_obj;
lean_object* v_a_780_ = stack[8].m_obj;
lean_object* v_a_781_ = stack[9].m_obj;
lean_object* v_a_782_ = stack[10].m_obj;
lean_object* v_a_783_ = stack[11].m_obj;
lean_object* v_a_784_ = stack[12].m_obj;
lean_object* v_res_820_;
v_res_820_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_772_, v_k_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
stack->m_obj
 = v_res_820_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_821_, lean_object* v_k_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_821_, v_k_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_k_822_);
return v_res_835_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0(lean_object* v_00_u03b1_836_, lean_object* v_msg_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v_msg_837_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_850_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_837_ = stack[1].m_obj;
lean_object* v___y_838_ = stack[2].m_obj;
lean_object* v___y_839_ = stack[3].m_obj;
lean_object* v___y_840_ = stack[4].m_obj;
lean_object* v___y_841_ = stack[5].m_obj;
lean_object* v___y_842_ = stack[6].m_obj;
lean_object* v___y_843_ = stack[7].m_obj;
lean_object* v___y_844_ = stack[8].m_obj;
lean_object* v___y_845_ = stack[9].m_obj;
lean_object* v___y_846_ = stack[10].m_obj;
lean_object* v___y_847_ = stack[11].m_obj;
lean_object* v___y_848_ = stack[12].m_obj;
lean_object* v_res_851_;
v_res_851_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0(lean_box(0), v_msg_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___boxed(lean_object* v_00_u03b1_852_, lean_object* v_msg_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0(v_00_u03b1_852_, v_msg_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_866_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_867_, lean_object* v_k_868_, lean_object* v_m_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; uint8_t v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = 0;
v___x_885_ = 1;
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_887_, 0, v_a_883_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*3, v___x_884_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*3 + 1, v___x_885_);
v___x_888_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_868_, v_m_869_, v_p_867_, v___x_887_);
lean_dec_ref_known(v___x_887_, 3);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
if (lean_obj_tag(v_a_889_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_895_; 
v_val_893_ = lean_ctor_get(v_a_889_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_a_889_, 1);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_val_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_val_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_del_object(v___x_891_);
lean_dec(v_a_889_);
v___x_897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_898_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_897_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v___x_898_;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_a_900_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_888_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_888_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_m_869_);
lean_dec_ref(v_p_867_);
v_a_908_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_882_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_882_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_mulMonM_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_867_ = stack[0].m_obj;
lean_object* v_k_868_ = stack[1].m_obj;
lean_object* v_m_869_ = stack[2].m_obj;
lean_object* v_a_870_ = stack[3].m_obj;
lean_object* v_a_871_ = stack[4].m_obj;
lean_object* v_a_872_ = stack[5].m_obj;
lean_object* v_a_873_ = stack[6].m_obj;
lean_object* v_a_874_ = stack[7].m_obj;
lean_object* v_a_875_ = stack[8].m_obj;
lean_object* v_a_876_ = stack[9].m_obj;
lean_object* v_a_877_ = stack[10].m_obj;
lean_object* v_a_878_ = stack[11].m_obj;
lean_object* v_a_879_ = stack[12].m_obj;
lean_object* v_a_880_ = stack[13].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_867_, v_k_868_, v_m_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_917_, lean_object* v_k_918_, lean_object* v_m_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_917_, v_k_918_, v_m_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_k_918_);
return v_res_932_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_933_, lean_object* v_p_u2082_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; uint8_t v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = 0;
v___x_950_ = 1;
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_952_, 0, v_a_948_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*3, v___x_949_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*3 + 1, v___x_950_);
v___x_953_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_u2081_933_, v_p_u2082_934_, v___x_952_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec_ref_known(v___x_952_, 3);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
if (lean_obj_tag(v_a_954_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_960_; 
v_val_958_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v_a_954_, 1);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_val_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_956_);
lean_dec(v_a_954_);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_963_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_962_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
return v___x_963_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_953_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_953_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_p_u2082_934_);
lean_dec_ref(v_p_u2081_933_);
v_a_973_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_947_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_947_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_mulM_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_933_ = stack[0].m_obj;
lean_object* v_p_u2082_934_ = stack[1].m_obj;
lean_object* v_a_935_ = stack[2].m_obj;
lean_object* v_a_936_ = stack[3].m_obj;
lean_object* v_a_937_ = stack[4].m_obj;
lean_object* v_a_938_ = stack[5].m_obj;
lean_object* v_a_939_ = stack[6].m_obj;
lean_object* v_a_940_ = stack[7].m_obj;
lean_object* v_a_941_ = stack[8].m_obj;
lean_object* v_a_942_ = stack[9].m_obj;
lean_object* v_a_943_ = stack[10].m_obj;
lean_object* v_a_944_ = stack[11].m_obj;
lean_object* v_a_945_ = stack[12].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_933_, v_p_u2082_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_982_, lean_object* v_p_u2082_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_982_, v_p_u2082_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_996_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_997_, lean_object* v_p_u2082_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = 0;
v___x_1014_ = 1;
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1016_, 0, v_a_1012_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*3, v___x_1013_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*3 + 1, v___x_1014_);
v___x_1017_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_p_u2081_997_, v_p_u2082_998_, v___x_1016_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec_ref_known(v___x_1016_, 3);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1028_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
if (lean_obj_tag(v_a_1018_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1024_; 
v_val_1022_ = lean_ctor_get(v_a_1018_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v_a_1018_, 1);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v_val_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_val_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_del_object(v___x_1020_);
lean_dec(v_a_1018_);
v___x_1026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_runPoly_x21___redArg___closed__48);
v___x_1027_ = l_Lean_throwError___at___00Lean_Grind_CommRing_Poly_mulConstM_spec__0___redArg(v___x_1026_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1017_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1017_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_p_u2082_998_);
lean_dec_ref(v_p_u2081_997_);
v_a_1037_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1011_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1011_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_combineM_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_997_ = stack[0].m_obj;
lean_object* v_p_u2082_998_ = stack[1].m_obj;
lean_object* v_a_999_ = stack[2].m_obj;
lean_object* v_a_1000_ = stack[3].m_obj;
lean_object* v_a_1001_ = stack[4].m_obj;
lean_object* v_a_1002_ = stack[5].m_obj;
lean_object* v_a_1003_ = stack[6].m_obj;
lean_object* v_a_1004_ = stack[7].m_obj;
lean_object* v_a_1005_ = stack[8].m_obj;
lean_object* v_a_1006_ = stack[9].m_obj;
lean_object* v_a_1007_ = stack[10].m_obj;
lean_object* v_a_1008_ = stack[11].m_obj;
lean_object* v_a_1009_ = stack[12].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_997_, v_p_u2082_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1046_, lean_object* v_p_u2082_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1046_, v_p_u2082_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spolM_spec__0(lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_nat_to_int(v_a_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_nat_to_int(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__2(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1069_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__1, &l_Lean_Grind_CommRing_Poly_spolM___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__1);
v___x_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
lean_ctor_set(v___x_1070_, 2, v___x_1067_);
lean_ctor_set(v___x_1070_, 3, v___x_1068_);
lean_ctor_set(v___x_1070_, 4, v___x_1067_);
return v___x_1070_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1071_, lean_object* v_p_u2082_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
if (lean_obj_tag(v_p_u2081_1071_) == 1)
{
if (lean_obj_tag(v_p_u2082_1072_) == 1)
{
lean_object* v_k_1088_; lean_object* v_v_1089_; lean_object* v_p_1090_; lean_object* v_k_1091_; lean_object* v_v_1092_; lean_object* v_p_1093_; lean_object* v_m_1094_; lean_object* v_m_u2081_1095_; lean_object* v_m_u2082_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_g_1099_; lean_object* v___x_1100_; lean_object* v_c_u2081_1101_; lean_object* v___x_1102_; lean_object* v_c_u2082_1103_; lean_object* v___x_1104_; 
v_k_1088_ = lean_ctor_get(v_p_u2081_1071_, 0);
lean_inc(v_k_1088_);
v_v_1089_ = lean_ctor_get(v_p_u2081_1071_, 1);
lean_inc_n(v_v_1089_, 2);
v_p_1090_ = lean_ctor_get(v_p_u2081_1071_, 2);
lean_inc_ref(v_p_1090_);
lean_dec_ref_known(v_p_u2081_1071_, 3);
v_k_1091_ = lean_ctor_get(v_p_u2082_1072_, 0);
lean_inc(v_k_1091_);
v_v_1092_ = lean_ctor_get(v_p_u2082_1072_, 1);
lean_inc_n(v_v_1092_, 2);
v_p_1093_ = lean_ctor_get(v_p_u2082_1072_, 2);
lean_inc_ref(v_p_1093_);
lean_dec_ref_known(v_p_u2082_1072_, 3);
v_m_1094_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1089_, v_v_1092_);
lean_inc(v_m_1094_);
v_m_u2081_1095_ = l_Lean_Grind_CommRing_Mon_div(v_m_1094_, v_v_1089_);
v_m_u2082_1096_ = l_Lean_Grind_CommRing_Mon_div(v_m_1094_, v_v_1092_);
v___x_1097_ = lean_nat_abs(v_k_1088_);
v___x_1098_ = lean_nat_abs(v_k_1091_);
v_g_1099_ = lean_nat_gcd(v___x_1097_, v___x_1098_);
lean_dec(v___x_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_nat_to_int(v_g_1099_);
v_c_u2081_1101_ = lean_int_ediv(v_k_1091_, v___x_1100_);
lean_dec(v_k_1091_);
v___x_1102_ = lean_int_neg(v_k_1088_);
lean_dec(v_k_1088_);
v_c_u2082_1103_ = lean_int_ediv(v___x_1102_, v___x_1100_);
lean_dec(v___x_1100_);
lean_dec(v___x_1102_);
lean_inc(v_m_u2081_1095_);
v___x_1104_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1090_, v_c_u2081_1101_, v_m_u2081_1095_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
lean_inc(v_m_u2082_1096_);
v___x_1106_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1093_, v_c_u2082_1103_, v_m_u2082_1096_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = l_Lean_Grind_CommRing_Poly_combineM(v_a_1105_, v_a_1107_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1109_);
lean_ctor_set(v___x_1113_, 1, v_c_u2081_1101_);
lean_ctor_set(v___x_1113_, 2, v_m_u2081_1095_);
lean_ctor_set(v___x_1113_, 3, v_c_u2082_1103_);
lean_ctor_set(v___x_1113_, 4, v_m_u2082_1096_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_c_u2082_1103_);
lean_dec(v_c_u2081_1101_);
lean_dec(v_m_u2082_1096_);
lean_dec(v_m_u2081_1095_);
v_a_1118_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1108_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1108_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
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
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1105_);
lean_dec(v_c_u2082_1103_);
lean_dec(v_c_u2081_1101_);
lean_dec(v_m_u2082_1096_);
lean_dec(v_m_u2081_1095_);
v_a_1126_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1106_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1106_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_c_u2082_1103_);
lean_dec(v_c_u2081_1101_);
lean_dec(v_m_u2082_1096_);
lean_dec(v_m_u2081_1095_);
lean_dec_ref(v_p_1093_);
v_a_1134_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1104_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1104_);
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
else
{
lean_dec_ref_known(v_p_u2081_1071_, 3);
lean_dec_ref(v_p_u2082_1072_);
goto v___jp_1085_;
}
}
else
{
lean_dec_ref(v_p_u2082_1072_);
lean_dec_ref(v_p_u2081_1071_);
goto v___jp_1085_;
}
v___jp_1085_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__2, &l_Lean_Grind_CommRing_Poly_spolM___closed__2_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__2);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_spolM_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1071_ = stack[0].m_obj;
lean_object* v_p_u2082_1072_ = stack[1].m_obj;
lean_object* v_a_1073_ = stack[2].m_obj;
lean_object* v_a_1074_ = stack[3].m_obj;
lean_object* v_a_1075_ = stack[4].m_obj;
lean_object* v_a_1076_ = stack[5].m_obj;
lean_object* v_a_1077_ = stack[6].m_obj;
lean_object* v_a_1078_ = stack[7].m_obj;
lean_object* v_a_1079_ = stack[8].m_obj;
lean_object* v_a_1080_ = stack[9].m_obj;
lean_object* v_a_1081_ = stack[10].m_obj;
lean_object* v_a_1082_ = stack[11].m_obj;
lean_object* v_a_1083_ = stack[12].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1071_, v_p_u2082_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1143_, lean_object* v_p_u2082_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1143_, v_p_u2082_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1157_;
}
}
lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(lean_object* v_m_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
if (lean_obj_tag(v_m_1168_) == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
else
{
lean_object* v_p_1178_; lean_object* v_m_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_p_1178_ = lean_ctor_get(v_m_1168_, 0);
lean_inc_ref(v_p_1178_);
v_m_1179_ = lean_ctor_get(v_m_1168_, 1);
lean_inc(v_m_1179_);
lean_dec_ref_known(v_m_1168_, 2);
v___x_1180_ = l_Lean_instInhabitedExpr;
v___x_1181_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1169_, v_a_1170_, v_a_1173_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_toRingState_1183_; lean_object* v_vars_1184_; lean_object* v_x_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1252_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v_toRingState_1183_ = lean_ctor_get(v_a_1182_, 0);
lean_inc_ref(v_toRingState_1183_);
lean_dec(v_a_1182_);
v_vars_1184_ = lean_ctor_get(v_toRingState_1183_, 0);
lean_inc_ref(v_vars_1184_);
lean_dec_ref(v_toRingState_1183_);
v_x_1185_ = lean_ctor_get(v_p_1178_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_p_1178_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_p_1178_, 1);
lean_dec(v_unused_1253_);
v___x_1187_ = v_p_1178_;
v_isShared_1188_ = v_isSharedCheck_1252_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_x_1185_);
lean_dec(v_p_1178_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1252_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___y_1190_; lean_object* v_size_1248_; uint8_t v___x_1249_; 
v_size_1248_ = lean_ctor_get(v_vars_1184_, 2);
v___x_1249_ = lean_nat_dec_lt(v_x_1185_, v_size_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref(v_vars_1184_);
v___x_1250_ = l_outOfBounds___redArg(v___x_1180_);
v___y_1190_ = v___x_1250_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1180_, v_vars_1184_, v_x_1185_);
lean_dec_ref(v_vars_1184_);
v___y_1190_ = v___x_1251_;
goto v___jp_1189_;
}
v___jp_1189_:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = l_Lean_Expr_cleanupAnnotations(v___y_1190_);
v___x_1192_ = l_Lean_Expr_isApp(v___x_1191_);
if (v___x_1192_ == 0)
{
lean_dec_ref(v___x_1191_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v_arg_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v_arg_1194_ = lean_ctor_get(v___x_1191_, 1);
lean_inc_ref(v_arg_1194_);
v___x_1195_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1191_);
v___x_1196_ = l_Lean_Expr_isApp(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_arg_1194_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1195_);
v___x_1199_ = l_Lean_Expr_isApp(v___x_1198_);
if (v___x_1199_ == 0)
{
lean_dec_ref(v___x_1198_);
lean_dec_ref(v_arg_1194_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1198_);
v___x_1202_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__2));
v___x_1203_ = l_Lean_Expr_isConstOf(v___x_1201_, v___x_1202_);
lean_dec_ref(v___x_1201_);
if (v___x_1203_ == 0)
{
lean_dec_ref(v_arg_1194_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = l_Lean_Expr_cleanupAnnotations(v_arg_1194_);
v___x_1206_ = l_Lean_Expr_isApp(v___x_1205_);
if (v___x_1206_ == 0)
{
lean_dec_ref(v___x_1205_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1205_);
v___x_1209_ = l_Lean_Expr_isApp(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_dec_ref(v___x_1208_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v_arg_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_arg_1211_ = lean_ctor_get(v___x_1208_, 1);
lean_inc_ref(v_arg_1211_);
v___x_1212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1208_);
v___x_1213_ = l_Lean_Expr_isApp(v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_arg_1211_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1212_);
v___x_1216_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___closed__5));
v___x_1217_ = l_Lean_Expr_isConstOf(v___x_1215_, v___x_1216_);
lean_dec_ref(v___x_1215_);
if (v___x_1217_ == 0)
{
lean_dec_ref(v_arg_1211_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_getNatValue_x3f(v_arg_1211_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec_ref(v_arg_1211_);
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
if (lean_obj_tag(v_a_1220_) == 1)
{
lean_object* v_val_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_m_1179_);
v_val_1224_ = lean_ctor_get(v_a_1220_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_a_1220_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1226_ = v_a_1220_;
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_val_1224_);
lean_dec(v_a_1220_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v_x_1185_);
lean_ctor_set(v___x_1187_, 0, v_val_1224_);
v___x_1229_ = v___x_1187_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_val_1224_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_x_1185_);
v___x_1229_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1231_);
v___x_1233_ = v___x_1222_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
else
{
lean_del_object(v___x_1222_);
lean_dec(v_a_1220_);
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
v_m_1168_ = v_m_1179_;
goto _start;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_del_object(v___x_1187_);
lean_dec(v_x_1185_);
lean_dec(v_m_1179_);
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
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_m_1179_);
lean_dec_ref(v_p_1178_);
v_a_1254_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1181_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1181_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1168_ = stack[0].m_obj;
lean_object* v_a_1169_ = stack[1].m_obj;
lean_object* v_a_1170_ = stack[2].m_obj;
lean_object* v_a_1171_ = stack[3].m_obj;
lean_object* v_a_1172_ = stack[4].m_obj;
lean_object* v_a_1173_ = stack[5].m_obj;
lean_object* v_a_1174_ = stack[6].m_obj;
lean_object* v_res_1262_;
v_res_1262_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_m_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
stack->m_obj
 = v_res_1262_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg___boxed(lean_object* v_m_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_m_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
return v_res_1271_;
}
}
lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_m_1272_, v_a_1273_, v_a_1274_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1272_ = stack[0].m_obj;
lean_object* v_a_1273_ = stack[1].m_obj;
lean_object* v_a_1274_ = stack[2].m_obj;
lean_object* v_a_1275_ = stack[3].m_obj;
lean_object* v_a_1276_ = stack[4].m_obj;
lean_object* v_a_1277_ = stack[5].m_obj;
lean_object* v_a_1278_ = stack[6].m_obj;
lean_object* v_a_1279_ = stack[7].m_obj;
lean_object* v_a_1280_ = stack[8].m_obj;
lean_object* v_a_1281_ = stack[9].m_obj;
lean_object* v_a_1282_ = stack[10].m_obj;
lean_object* v_a_1283_ = stack[11].m_obj;
lean_object* v_res_1286_;
v_res_1286_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
stack->m_obj
 = v_res_1286_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
return v_res_1300_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(lean_object* v_p_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
if (lean_obj_tag(v_p_1301_) == 0)
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v_p_1301_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v_p_1301_, 0);
lean_dec(v_unused_1317_);
v___x_1310_ = v_p_1301_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v_p_1301_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_v_1318_; lean_object* v_p_1319_; lean_object* v___x_1320_; 
v_v_1318_ = lean_ctor_get(v_p_1301_, 1);
lean_inc(v_v_1318_);
v_p_1319_ = lean_ctor_get(v_p_1301_, 2);
lean_inc_ref(v_p_1319_);
lean_dec_ref_known(v_p_1301_, 3);
v___x_1320_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___redArg(v_v_1318_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
if (lean_obj_tag(v_a_1321_) == 1)
{
lean_dec_ref(v_p_1319_);
return v___x_1320_;
}
else
{
lean_dec_ref_known(v___x_1320_, 1);
v_p_1301_ = v_p_1319_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1319_);
return v___x_1320_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1301_ = stack[0].m_obj;
lean_object* v_a_1302_ = stack[1].m_obj;
lean_object* v_a_1303_ = stack[2].m_obj;
lean_object* v_a_1304_ = stack[3].m_obj;
lean_object* v_a_1305_ = stack[4].m_obj;
lean_object* v_a_1306_ = stack[5].m_obj;
lean_object* v_a_1307_ = stack[6].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(v_p_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg___boxed(lean_object* v_p_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(v_p_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
return v_res_1332_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(v_p_1333_, v_a_1334_, v_a_1335_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1333_ = stack[0].m_obj;
lean_object* v_a_1334_ = stack[1].m_obj;
lean_object* v_a_1335_ = stack[2].m_obj;
lean_object* v_a_1336_ = stack[3].m_obj;
lean_object* v_a_1337_ = stack[4].m_obj;
lean_object* v_a_1338_ = stack[5].m_obj;
lean_object* v_a_1339_ = stack[6].m_obj;
lean_object* v_a_1340_ = stack[7].m_obj;
lean_object* v_a_1341_ = stack[8].m_obj;
lean_object* v_a_1342_ = stack[9].m_obj;
lean_object* v_a_1343_ = stack[10].m_obj;
lean_object* v_a_1344_ = stack[11].m_obj;
lean_object* v_res_1347_;
v_res_1347_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
stack->m_obj
 = v_res_1347_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1361_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object* v_k_u2082_x27_1362_, lean_object* v_m_u2082_1363_, lean_object* v_p_u2082_1364_, uint8_t v_checkCoeff_1365_, lean_object* v_p_u2081_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
if (lean_obj_tag(v_p_u2081_1366_) == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref_known(v_p_u2081_1366_, 1);
lean_dec_ref(v_p_u2082_1364_);
lean_dec(v_m_u2082_1363_);
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
else
{
lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_p_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1524_; 
v_k_1381_ = lean_ctor_get(v_p_u2081_1366_, 0);
v_v_1382_ = lean_ctor_get(v_p_u2081_1366_, 1);
v_p_1383_ = lean_ctor_get(v_p_u2081_1366_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_p_u2081_1366_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1385_ = v_p_u2081_1366_;
v_isShared_1386_ = v_isSharedCheck_1524_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_p_1383_);
lean_inc(v_v_1382_);
lean_inc(v_k_1381_);
lean_dec(v_p_u2081_1366_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1524_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
uint8_t v___y_1388_; uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_1363_, v_v_1382_);
if (v___x_1520_ == 0)
{
v___y_1388_ = v___x_1520_;
goto v___jp_1387_;
}
else
{
if (v_checkCoeff_1365_ == 0)
{
v___y_1388_ = v___x_1520_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_int_emod(v_k_1381_, v_k_u2082_x27_1362_);
v___x_1522_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1523_ = lean_int_dec_eq(v___x_1521_, v___x_1522_);
lean_dec(v___x_1521_);
v___y_1388_ = v___x_1523_;
goto v___jp_1387_;
}
}
v___jp_1387_:
{
if (v___y_1388_ == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1362_, v_m_u2082_1363_, v_p_u2082_1364_, v_checkCoeff_1365_, v_p_1383_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1472_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1472_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1472_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
if (lean_obj_tag(v_a_1390_) == 1)
{
lean_object* v_val_1394_; lean_object* v___x_1395_; 
lean_del_object(v___x_1392_);
v_val_1394_ = lean_ctor_get(v_a_1390_, 0);
lean_inc(v_val_1394_);
v___x_1395_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00Lean_Grind_CommRing_Expr_toPolyM_x3f_spec__0(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1459_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1459_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1459_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_a_1396_) == 1)
{
lean_object* v_val_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1432_; 
v_val_1400_ = lean_ctor_get(v_a_1396_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1402_ = v_a_1396_;
v_isShared_1403_ = v_isSharedCheck_1432_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_val_1400_);
lean_dec(v_a_1396_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1432_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_p_1404_; lean_object* v_k_u2081_1405_; lean_object* v_k_u2082_1406_; lean_object* v_m_u2082_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1431_; 
v_p_1404_ = lean_ctor_get(v_val_1394_, 0);
v_k_u2081_1405_ = lean_ctor_get(v_val_1394_, 1);
v_k_u2082_1406_ = lean_ctor_get(v_val_1394_, 2);
v_m_u2082_1407_ = lean_ctor_get(v_val_1394_, 3);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_val_1394_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1409_ = v_val_1394_;
v_isShared_1410_ = v_isSharedCheck_1431_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_m_u2082_1407_);
lean_inc(v_k_u2082_1406_);
lean_inc(v_k_u2081_1405_);
lean_inc(v_p_1404_);
lean_dec(v_val_1394_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1431_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1411_ = lean_int_mul(v_k_1381_, v_k_u2081_1405_);
lean_dec(v_k_1381_);
v___x_1412_ = lean_nat_to_int(v_val_1400_);
v___x_1413_ = lean_int_emod(v___x_1411_, v___x_1412_);
lean_dec(v___x_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1415_ = lean_int_dec_eq(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref_known(v_a_1390_, 1);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 2, v_p_1404_);
lean_ctor_set(v___x_1385_, 0, v___x_1413_);
v___x_1417_ = v___x_1385_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_p_1404_);
v___x_1417_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1417_);
v___x_1419_ = v___x_1409_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_u2081_1405_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_k_u2082_1406_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_m_u2082_1407_);
v___x_1419_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1419_);
v___x_1421_ = v___x_1402_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1421_);
v___x_1423_ = v___x_1398_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
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
else
{
lean_object* v___x_1429_; 
lean_dec(v___x_1413_);
lean_del_object(v___x_1409_);
lean_dec(v_m_u2082_1407_);
lean_dec(v_k_u2082_1406_);
lean_dec(v_k_u2081_1405_);
lean_dec_ref(v_p_1404_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1385_);
lean_dec(v_v_1382_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_a_1390_);
v___x_1429_ = v___x_1398_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1390_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
else
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1396_);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_a_1390_, 0);
lean_dec(v_unused_1458_);
v___x_1434_ = v_a_1390_;
v_isShared_1435_ = v_isSharedCheck_1457_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v_a_1390_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1457_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_p_1436_; lean_object* v_k_u2081_1437_; lean_object* v_k_u2082_1438_; lean_object* v_m_u2082_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1456_; 
v_p_1436_ = lean_ctor_get(v_val_1394_, 0);
v_k_u2081_1437_ = lean_ctor_get(v_val_1394_, 1);
v_k_u2082_1438_ = lean_ctor_get(v_val_1394_, 2);
v_m_u2082_1439_ = lean_ctor_get(v_val_1394_, 3);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_val_1394_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1441_ = v_val_1394_;
v_isShared_1442_ = v_isSharedCheck_1456_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_m_u2082_1439_);
lean_inc(v_k_u2082_1438_);
lean_inc(v_k_u2081_1437_);
lean_inc(v_p_1436_);
lean_dec(v_val_1394_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1456_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_int_mul(v_k_1381_, v_k_u2081_1437_);
lean_dec(v_k_1381_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 2, v_p_1436_);
lean_ctor_set(v___x_1385_, 0, v___x_1443_);
v___x_1445_ = v___x_1385_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_p_1436_);
v___x_1445_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1445_);
v___x_1447_ = v___x_1441_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_u2081_1437_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_k_u2082_1438_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_m_u2082_1439_);
v___x_1447_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1447_);
v___x_1449_ = v___x_1434_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1451_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1449_);
v___x_1451_ = v___x_1398_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
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
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref_known(v_a_1390_, 1);
lean_dec(v_val_1394_);
lean_del_object(v___x_1385_);
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
v_a_1460_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1395_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1395_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v_a_1390_);
lean_del_object(v___x_1385_);
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
v___x_1468_ = lean_box(0);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1468_);
v___x_1470_ = v___x_1392_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_del_object(v___x_1385_);
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
return v___x_1389_;
}
}
else
{
lean_object* v_m_u2082_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_g_1476_; lean_object* v___x_1477_; lean_object* v_k_u2081_1478_; lean_object* v___x_1479_; lean_object* v_k_u2082_1480_; lean_object* v___x_1481_; 
lean_del_object(v___x_1385_);
v_m_u2082_1473_ = l_Lean_Grind_CommRing_Mon_div(v_v_1382_, v_m_u2082_1363_);
v___x_1474_ = lean_nat_abs(v_k_1381_);
v___x_1475_ = lean_nat_abs(v_k_u2082_x27_1362_);
v_g_1476_ = lean_nat_gcd(v___x_1474_, v___x_1475_);
lean_dec(v___x_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_nat_to_int(v_g_1476_);
v_k_u2081_1478_ = lean_int_ediv(v_k_u2082_x27_1362_, v___x_1477_);
v___x_1479_ = lean_int_neg(v_k_1381_);
lean_dec(v_k_1381_);
v_k_u2082_1480_ = lean_int_ediv(v___x_1479_, v___x_1477_);
lean_dec(v___x_1477_);
lean_dec(v___x_1479_);
lean_inc(v_m_u2082_1473_);
v___x_1481_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_u2082_1364_, v_k_u2082_1480_, v_m_u2082_1473_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1383_, v_k_u2081_1478_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_Grind_CommRing_Poly_combineM(v_a_1482_, v_a_1484_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1495_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1486_);
lean_ctor_set(v___x_1490_, 1, v_k_u2081_1478_);
lean_ctor_set(v___x_1490_, 2, v_k_u2082_1480_);
lean_ctor_set(v___x_1490_, 3, v_m_u2082_1473_);
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1491_);
v___x_1493_ = v___x_1488_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_k_u2082_1480_);
lean_dec(v_k_u2081_1478_);
lean_dec(v_m_u2082_1473_);
v_a_1496_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1485_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_a_1482_);
lean_dec(v_k_u2082_1480_);
lean_dec(v_k_u2081_1478_);
lean_dec(v_m_u2082_1473_);
v_a_1504_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1483_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1483_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_k_u2082_1480_);
lean_dec(v_k_u2081_1478_);
lean_dec(v_m_u2082_1473_);
lean_dec_ref(v_p_1383_);
v_a_1512_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1481_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1481_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_u2082_x27_1362_ = stack[0].m_obj;
lean_object* v_m_u2082_1363_ = stack[1].m_obj;
lean_object* v_p_u2082_1364_ = stack[2].m_obj;
uint8_t v_checkCoeff_1365_ = stack[3].m_num;
lean_object* v_p_u2081_1366_ = stack[4].m_obj;
lean_object* v_a_1367_ = stack[5].m_obj;
lean_object* v_a_1368_ = stack[6].m_obj;
lean_object* v_a_1369_ = stack[7].m_obj;
lean_object* v_a_1370_ = stack[8].m_obj;
lean_object* v_a_1371_ = stack[9].m_obj;
lean_object* v_a_1372_ = stack[10].m_obj;
lean_object* v_a_1373_ = stack[11].m_obj;
lean_object* v_a_1374_ = stack[12].m_obj;
lean_object* v_a_1375_ = stack[13].m_obj;
lean_object* v_a_1376_ = stack[14].m_obj;
lean_object* v_a_1377_ = stack[15].m_obj;
lean_object* v_res_1525_;
v_res_1525_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1362_, v_m_u2082_1363_, v_p_u2082_1364_, v_checkCoeff_1365_, v_p_u2081_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
stack->m_obj
 = v_res_1525_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object** _args){
lean_object* v_k_u2082_x27_1526_ = _args[0];
lean_object* v_m_u2082_1527_ = _args[1];
lean_object* v_p_u2082_1528_ = _args[2];
lean_object* v_checkCoeff_1529_ = _args[3];
lean_object* v_p_u2081_1530_ = _args[4];
lean_object* v_a_1531_ = _args[5];
lean_object* v_a_1532_ = _args[6];
lean_object* v_a_1533_ = _args[7];
lean_object* v_a_1534_ = _args[8];
lean_object* v_a_1535_ = _args[9];
lean_object* v_a_1536_ = _args[10];
lean_object* v_a_1537_ = _args[11];
lean_object* v_a_1538_ = _args[12];
lean_object* v_a_1539_ = _args[13];
lean_object* v_a_1540_ = _args[14];
lean_object* v_a_1541_ = _args[15];
lean_object* v_a_1542_ = _args[16];
_start:
{
uint8_t v_checkCoeff_boxed_1543_; lean_object* v_res_1544_; 
v_checkCoeff_boxed_1543_ = lean_unbox(v_checkCoeff_1529_);
v_res_1544_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1526_, v_m_u2082_1527_, v_p_u2082_1528_, v_checkCoeff_boxed_1543_, v_p_u2081_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_k_u2082_x27_1526_);
return v_res_1544_;
}
}
lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object* v_p_u2081_1545_, lean_object* v_p_u2082_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
if (lean_obj_tag(v_p_u2082_1546_) == 1)
{
lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_p_1561_; lean_object* v___x_1562_; 
v_k_1559_ = lean_ctor_get(v_p_u2082_1546_, 0);
lean_inc(v_k_1559_);
v_v_1560_ = lean_ctor_get(v_p_u2082_1546_, 1);
lean_inc(v_v_1560_);
v_p_1561_ = lean_ctor_get(v_p_u2082_1546_, 2);
lean_inc_ref(v_p_1561_);
lean_dec_ref_known(v_p_u2082_1546_, 3);
v___x_1562_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_1547_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1564_) == 0)
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_unbox(v_a_1563_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = lean_unbox(v_a_1563_);
lean_dec(v_a_1563_);
v___x_1567_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1559_, v_v_1560_, v_p_1561_, v___x_1566_, v_p_u2081_1545_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_k_1559_);
return v___x_1567_;
}
else
{
lean_object* v_a_1568_; uint8_t v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1569_ = lean_unbox(v_a_1568_);
lean_dec(v_a_1568_);
if (v___x_1569_ == 0)
{
uint8_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_unbox(v_a_1563_);
lean_dec(v_a_1563_);
v___x_1571_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1559_, v_v_1560_, v_p_1561_, v___x_1570_, v_p_u2081_1545_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_k_1559_);
return v___x_1571_;
}
else
{
uint8_t v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v_a_1563_);
v___x_1572_ = 0;
v___x_1573_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1559_, v_v_1560_, v_p_1561_, v___x_1572_, v_p_u2081_1545_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_k_1559_);
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_a_1563_);
lean_dec_ref(v_p_1561_);
lean_dec(v_v_1560_);
lean_dec(v_k_1559_);
lean_dec_ref(v_p_u2081_1545_);
v_a_1574_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1564_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1564_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_p_1561_);
lean_dec(v_v_1560_);
lean_dec(v_k_1559_);
lean_dec_ref(v_p_u2081_1545_);
v_a_1582_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1562_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1562_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec_ref(v_p_u2082_1546_);
lean_dec_ref(v_p_u2081_1545_);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_simpM_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1545_ = stack[0].m_obj;
lean_object* v_p_u2082_1546_ = stack[1].m_obj;
lean_object* v_a_1547_ = stack[2].m_obj;
lean_object* v_a_1548_ = stack[3].m_obj;
lean_object* v_a_1549_ = stack[4].m_obj;
lean_object* v_a_1550_ = stack[5].m_obj;
lean_object* v_a_1551_ = stack[6].m_obj;
lean_object* v_a_1552_ = stack[7].m_obj;
lean_object* v_a_1553_ = stack[8].m_obj;
lean_object* v_a_1554_ = stack[9].m_obj;
lean_object* v_a_1555_ = stack[10].m_obj;
lean_object* v_a_1556_ = stack[11].m_obj;
lean_object* v_a_1557_ = stack[12].m_obj;
lean_object* v_res_1592_;
v_res_1592_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(v_p_u2081_1545_, v_p_u2082_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
stack->m_obj
 = v_res_1592_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object* v_p_u2081_1593_, lean_object* v_p_u2082_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(v_p_u2081_1593_, v_p_u2082_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1607_;
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
