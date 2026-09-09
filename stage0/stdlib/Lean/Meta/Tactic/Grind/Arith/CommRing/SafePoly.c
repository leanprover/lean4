// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM public import Lean.Meta.Sym.Arith.Poly import Lean.Meta.Tactic.Grind.Arith.EvalNum import Init.Data.Nat.Internal.Linear
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spolM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spolM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value;
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value;
static const lean_string_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(lean_object* v___y_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_37_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_37_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_37_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_37_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_toRing_23_; lean_object* v_charInst_x3f_24_; 
v_toRing_23_ = lean_ctor_get(v_a_14_, 0);
lean_inc_ref(v_toRing_23_);
lean_dec(v_a_14_);
v_charInst_x3f_24_ = lean_ctor_get(v_toRing_23_, 5);
lean_inc(v_charInst_x3f_24_);
lean_dec_ref(v_toRing_23_);
if (lean_obj_tag(v_charInst_x3f_24_) == 1)
{
lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_36_; 
v_val_25_ = lean_ctor_get(v_charInst_x3f_24_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v_charInst_x3f_24_);
if (v_isSharedCheck_36_ == 0)
{
v___x_27_ = v_charInst_x3f_24_;
v_isShared_28_ = v_isSharedCheck_36_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_dec(v_charInst_x3f_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_36_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_snd_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_snd_29_ = lean_ctor_get(v_val_25_, 1);
lean_inc(v_snd_29_);
lean_dec(v_val_25_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v_snd_29_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_33_; 
lean_del_object(v___x_16_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v_snd_29_);
v___x_33_ = v___x_27_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_snd_29_);
v___x_33_ = v_reuseFailAlloc_35_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
else
{
lean_dec(v_snd_29_);
lean_del_object(v___x_27_);
goto v___jp_18_;
}
}
}
else
{
lean_dec(v_charInst_x3f_24_);
goto v___jp_18_;
}
v___jp_18_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_box(0);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_19_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_13_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_13_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0___boxed(lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_nat_to_int(v_a_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_88_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_88_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
if (lean_obj_tag(v_a_75_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v_val_79_ = lean_ctor_get(v_a_75_, 0);
lean_inc(v_val_79_);
lean_dec_ref_known(v_a_75_, 1);
v___x_80_ = lean_nat_to_int(v_val_79_);
v___x_81_ = lean_int_emod(v_a_61_, v___x_80_);
lean_dec(v___x_80_);
lean_dec(v_a_61_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_81_);
v___x_83_ = v___x_77_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v_a_75_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_a_61_);
v___x_86_ = v___x_77_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_61_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_a_61_);
v_a_89_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_74_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_74_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar___boxed(lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(lean_object* v_p_111_, lean_object* v_k_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_139_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_139_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_139_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_139_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
if (lean_obj_tag(v_a_126_) == 1)
{
lean_object* v_val_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_val_130_ = lean_ctor_get(v_a_126_, 0);
lean_inc(v_val_130_);
lean_dec_ref_known(v_a_126_, 1);
v___x_131_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_111_, v_k_112_, v_val_130_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_137_; 
lean_dec(v_a_126_);
v___x_135_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_111_, v_k_112_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_135_);
v___x_137_ = v___x_128_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v_p_111_);
v_a_140_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_125_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_125_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst___boxed(lean_object* v_p_148_, lean_object* v_k_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_148_, v_k_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_k_149_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(lean_object* v_k_163_, lean_object* v_p_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_191_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_191_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
if (lean_obj_tag(v_a_178_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v_val_182_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_a_178_, 1);
v___x_183_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_163_, v_p_164_, v_val_182_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_dec(v_a_178_);
v___x_187_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_163_, v_p_164_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_187_);
v___x_189_ = v___x_180_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_p_164_);
v_a_192_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_177_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst___boxed(lean_object* v_k_200_, lean_object* v_p_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_200_, v_p_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_k_200_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(lean_object* v_k_215_, lean_object* v_m_216_, lean_object* v_p_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_244_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_244_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
if (lean_obj_tag(v_a_231_) == 1)
{
lean_object* v_val_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v_val_235_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_a_231_, 1);
v___x_236_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_215_, v_m_216_, v_p_217_, v_val_235_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_238_ = v___x_233_;
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
else
{
lean_object* v___x_240_; lean_object* v___x_242_; 
lean_dec(v_a_231_);
v___x_240_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_215_, v_m_216_, v_p_217_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_240_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_p_217_);
lean_dec(v_m_216_);
v_a_245_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_230_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_230_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon___boxed(lean_object* v_k_253_, lean_object* v_m_254_, lean_object* v_p_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_253_, v_m_254_, v_p_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_k_253_);
return v_res_268_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_Lean_maxRecDepthErrorMessage;
v___x_275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3);
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4);
v___x_279_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2));
v___x_280_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(lean_object* v_ref_281_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_ref_281_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___boxed(lean_object* v_ref_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(lean_object* v_00_u03b1_289_, lean_object* v_ref_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_290_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___boxed(lean_object* v_00_u03b1_304_, lean_object* v_ref_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(v_00_u03b1_304_, v_ref_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(lean_object* v_p_u2081_321_, lean_object* v_p_u2082_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_toCold_335_; lean_object* v_options_336_; lean_object* v_currRecDepth_337_; lean_object* v_maxRecDepth_338_; lean_object* v_ref_339_; lean_object* v_currNamespace_340_; lean_object* v_openDecls_341_; lean_object* v_initHeartbeats_342_; lean_object* v_maxHeartbeats_343_; lean_object* v_currMacroScope_344_; uint8_t v_diag_345_; uint8_t v_suppressElabErrors_346_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_toCold_335_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_toCold_335_);
v_options_336_ = lean_ctor_get(v_a_332_, 1);
lean_inc_ref(v_options_336_);
v_currRecDepth_337_ = lean_ctor_get(v_a_332_, 2);
lean_inc(v_currRecDepth_337_);
v_maxRecDepth_338_ = lean_ctor_get(v_a_332_, 3);
lean_inc(v_maxRecDepth_338_);
v_ref_339_ = lean_ctor_get(v_a_332_, 4);
lean_inc(v_ref_339_);
v_currNamespace_340_ = lean_ctor_get(v_a_332_, 5);
lean_inc(v_currNamespace_340_);
v_openDecls_341_ = lean_ctor_get(v_a_332_, 6);
lean_inc(v_openDecls_341_);
v_initHeartbeats_342_ = lean_ctor_get(v_a_332_, 7);
lean_inc(v_initHeartbeats_342_);
v_maxHeartbeats_343_ = lean_ctor_get(v_a_332_, 8);
lean_inc(v_maxHeartbeats_343_);
v_currMacroScope_344_ = lean_ctor_get(v_a_332_, 9);
lean_inc(v_currMacroScope_344_);
v_diag_345_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*10);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_332_);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_nat_dec_eq(v_maxRecDepth_338_, v___x_460_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = lean_nat_dec_eq(v_currRecDepth_337_, v_maxRecDepth_338_);
if (v___x_462_ == 0)
{
goto v___jp_347_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v_currMacroScope_344_);
lean_dec(v_maxHeartbeats_343_);
lean_dec(v_initHeartbeats_342_);
lean_dec(v_openDecls_341_);
lean_dec(v_currNamespace_340_);
lean_dec(v_maxRecDepth_338_);
lean_dec(v_currRecDepth_337_);
lean_dec_ref(v_options_336_);
lean_dec_ref(v_toCold_335_);
lean_dec_ref(v_p_u2082_322_);
lean_dec_ref(v_p_u2081_321_);
v___x_463_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_339_);
return v___x_463_;
}
}
else
{
goto v___jp_347_;
}
v___jp_347_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_currRecDepth_337_, v___x_348_);
lean_dec(v_currRecDepth_337_);
v___x_350_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_350_, 0, v_toCold_335_);
lean_ctor_set(v___x_350_, 1, v_options_336_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_ctor_set(v___x_350_, 3, v_maxRecDepth_338_);
lean_ctor_set(v___x_350_, 4, v_ref_339_);
lean_ctor_set(v___x_350_, 5, v_currNamespace_340_);
lean_ctor_set(v___x_350_, 6, v_openDecls_341_);
lean_ctor_set(v___x_350_, 7, v_initHeartbeats_342_);
lean_ctor_set(v___x_350_, 8, v_maxHeartbeats_343_);
lean_ctor_set(v___x_350_, 9, v_currMacroScope_344_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*10, v_diag_345_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*10 + 1, v_suppressElabErrors_346_);
if (lean_obj_tag(v_p_u2081_321_) == 0)
{
if (lean_obj_tag(v_p_u2082_322_) == 0)
{
lean_object* v_k_351_; lean_object* v_k_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_377_; 
v_k_351_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_inc(v_k_351_);
lean_dec_ref_known(v_p_u2081_321_, 1);
v_k_352_ = lean_ctor_get(v_p_u2082_322_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_377_ == 0)
{
v___x_354_ = v_p_u2082_322_;
v_isShared_355_ = v_isSharedCheck_377_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_k_352_);
lean_dec(v_p_u2082_322_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_377_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_int_add(v_k_351_, v_k_352_);
lean_dec(v_k_352_);
lean_dec(v_k_351_);
v___x_357_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_356_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
lean_dec_ref_known(v___x_350_, 10);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_368_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v_a_358_);
v___x_363_ = v___x_354_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_del_object(v___x_354_);
v_a_369_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_357_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_357_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
else
{
lean_object* v_k_378_; lean_object* v___x_379_; 
v_k_378_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_inc(v_k_378_);
lean_dec_ref_known(v_p_u2081_321_, 1);
v___x_379_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2082_322_, v_k_378_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
lean_dec_ref_known(v___x_350_, 10);
lean_dec(v_k_378_);
return v___x_379_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_322_) == 0)
{
lean_object* v_k_380_; lean_object* v___x_381_; 
v_k_380_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_inc(v_k_380_);
lean_dec_ref_known(v_p_u2082_322_, 1);
v___x_381_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2081_321_, v_k_380_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
lean_dec_ref_known(v___x_350_, 10);
lean_dec(v_k_380_);
return v___x_381_;
}
else
{
lean_object* v_k_382_; lean_object* v_v_383_; lean_object* v_p_384_; lean_object* v_k_385_; lean_object* v_v_386_; lean_object* v_p_387_; uint8_t v___x_388_; 
v_k_382_ = lean_ctor_get(v_p_u2081_321_, 0);
v_v_383_ = lean_ctor_get(v_p_u2081_321_, 1);
v_p_384_ = lean_ctor_get(v_p_u2081_321_, 2);
v_k_385_ = lean_ctor_get(v_p_u2082_322_, 0);
v_v_386_ = lean_ctor_get(v_p_u2082_322_, 1);
v_p_387_ = lean_ctor_get(v_p_u2082_322_, 2);
v___x_388_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_383_, v_v_386_);
switch(v___x_388_)
{
case 0:
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_404_; 
lean_inc_ref(v_p_387_);
lean_inc(v_v_386_);
lean_inc(v_k_385_);
v_isSharedCheck_404_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_405_ = lean_ctor_get(v_p_u2082_322_, 2);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_p_u2082_322_, 1);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_dec(v_unused_407_);
v___x_390_ = v_p_u2082_322_;
v_isShared_391_ = v_isSharedCheck_404_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_p_u2082_322_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_404_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; 
v___x_392_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_321_, v_p_387_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_403_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_403_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 2, v_a_393_);
v___x_398_ = v___x_390_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_k_385_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_v_386_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_a_393_);
v___x_398_ = v_reuseFailAlloc_402_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_del_object(v___x_390_);
lean_dec(v_v_386_);
lean_dec(v_k_385_);
return v___x_392_;
}
}
}
case 1:
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_437_; 
lean_inc_ref(v_p_387_);
lean_inc(v_k_385_);
lean_inc_ref(v_p_384_);
lean_inc(v_v_383_);
lean_inc(v_k_382_);
lean_dec_ref_known(v_p_u2081_321_, 3);
v_isSharedCheck_437_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; lean_object* v_unused_439_; lean_object* v_unused_440_; 
v_unused_438_ = lean_ctor_get(v_p_u2082_322_, 2);
lean_dec(v_unused_438_);
v_unused_439_ = lean_ctor_get(v_p_u2082_322_, 1);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_dec(v_unused_440_);
v___x_409_ = v_p_u2082_322_;
v_isShared_410_ = v_isSharedCheck_437_;
goto v_resetjp_408_;
}
else
{
lean_dec(v_p_u2082_322_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_437_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_int_add(v_k_382_, v_k_385_);
lean_dec(v_k_385_);
lean_dec(v_k_382_);
v___x_412_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_411_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_415_ = lean_int_dec_eq(v_a_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_384_, v_p_387_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_427_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_427_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 2, v_a_417_);
lean_ctor_set(v___x_409_, 1, v_v_383_);
lean_ctor_set(v___x_409_, 0, v_a_413_);
v___x_422_ = v___x_409_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_v_383_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_a_417_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_dec(v_a_413_);
lean_del_object(v___x_409_);
lean_dec(v_v_383_);
return v___x_416_;
}
}
else
{
lean_dec(v_a_413_);
lean_del_object(v___x_409_);
lean_dec(v_v_383_);
v_p_u2081_321_ = v_p_384_;
v_p_u2082_322_ = v_p_387_;
v_a_332_ = v___x_350_;
goto _start;
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_del_object(v___x_409_);
lean_dec_ref(v_p_387_);
lean_dec_ref(v_p_384_);
lean_dec(v_v_383_);
lean_dec_ref_known(v___x_350_, 10);
v_a_429_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_412_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_412_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
default: 
{
lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_456_; 
lean_inc_ref(v_p_384_);
lean_inc(v_v_383_);
lean_inc(v_k_382_);
v_isSharedCheck_456_ = !lean_is_exclusive(v_p_u2081_321_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_457_ = lean_ctor_get(v_p_u2081_321_, 2);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_p_u2081_321_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_dec(v_unused_459_);
v___x_442_ = v_p_u2081_321_;
v_isShared_443_ = v_isSharedCheck_456_;
goto v_resetjp_441_;
}
else
{
lean_dec(v_p_u2081_321_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_456_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; 
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_384_, v_p_u2082_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_350_, v_a_333_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_455_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 2, v_a_445_);
v___x_450_ = v___x_442_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_k_382_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_v_383_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_a_445_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
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
lean_del_object(v___x_442_);
lean_dec(v_v_383_);
lean_dec(v_k_382_);
return v___x_444_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object* v_p_u2081_464_, lean_object* v_p_u2082_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_464_, v_p_u2082_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object* v_p_u2081_479_, lean_object* v_p_u2082_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_, lean_object* v_h__3_483_, lean_object* v_h__4_484_){
_start:
{
if (lean_obj_tag(v_p_u2081_479_) == 0)
{
lean_dec(v_h__4_484_);
lean_dec(v_h__3_483_);
if (lean_obj_tag(v_p_u2082_480_) == 0)
{
lean_object* v_k_485_; lean_object* v_k_486_; lean_object* v___x_487_; 
lean_dec(v_h__2_482_);
v_k_485_ = lean_ctor_get(v_p_u2081_479_, 0);
lean_inc(v_k_485_);
lean_dec_ref_known(v_p_u2081_479_, 1);
v_k_486_ = lean_ctor_get(v_p_u2082_480_, 0);
lean_inc(v_k_486_);
lean_dec_ref_known(v_p_u2082_480_, 1);
v___x_487_ = lean_apply_2(v_h__1_481_, v_k_485_, v_k_486_);
return v___x_487_;
}
else
{
lean_object* v_k_488_; lean_object* v_k_489_; lean_object* v_v_490_; lean_object* v_p_491_; lean_object* v___x_492_; 
lean_dec(v_h__1_481_);
v_k_488_ = lean_ctor_get(v_p_u2081_479_, 0);
lean_inc(v_k_488_);
lean_dec_ref_known(v_p_u2081_479_, 1);
v_k_489_ = lean_ctor_get(v_p_u2082_480_, 0);
lean_inc(v_k_489_);
v_v_490_ = lean_ctor_get(v_p_u2082_480_, 1);
lean_inc(v_v_490_);
v_p_491_ = lean_ctor_get(v_p_u2082_480_, 2);
lean_inc_ref(v_p_491_);
lean_dec_ref_known(v_p_u2082_480_, 3);
v___x_492_ = lean_apply_4(v_h__2_482_, v_k_488_, v_k_489_, v_v_490_, v_p_491_);
return v___x_492_;
}
}
else
{
lean_dec(v_h__2_482_);
lean_dec(v_h__1_481_);
if (lean_obj_tag(v_p_u2082_480_) == 0)
{
lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_p_495_; lean_object* v_k_496_; lean_object* v___x_497_; 
lean_dec(v_h__4_484_);
v_k_493_ = lean_ctor_get(v_p_u2081_479_, 0);
lean_inc(v_k_493_);
v_v_494_ = lean_ctor_get(v_p_u2081_479_, 1);
lean_inc(v_v_494_);
v_p_495_ = lean_ctor_get(v_p_u2081_479_, 2);
lean_inc_ref(v_p_495_);
lean_dec_ref_known(v_p_u2081_479_, 3);
v_k_496_ = lean_ctor_get(v_p_u2082_480_, 0);
lean_inc(v_k_496_);
lean_dec_ref_known(v_p_u2082_480_, 1);
v___x_497_ = lean_apply_4(v_h__3_483_, v_k_493_, v_v_494_, v_p_495_, v_k_496_);
return v___x_497_;
}
else
{
lean_object* v_k_498_; lean_object* v_v_499_; lean_object* v_p_500_; lean_object* v_k_501_; lean_object* v_v_502_; lean_object* v_p_503_; lean_object* v___x_504_; 
lean_dec(v_h__3_483_);
v_k_498_ = lean_ctor_get(v_p_u2081_479_, 0);
lean_inc(v_k_498_);
v_v_499_ = lean_ctor_get(v_p_u2081_479_, 1);
lean_inc(v_v_499_);
v_p_500_ = lean_ctor_get(v_p_u2081_479_, 2);
lean_inc_ref(v_p_500_);
lean_dec_ref_known(v_p_u2081_479_, 3);
v_k_501_ = lean_ctor_get(v_p_u2082_480_, 0);
lean_inc(v_k_501_);
v_v_502_ = lean_ctor_get(v_p_u2082_480_, 1);
lean_inc(v_v_502_);
v_p_503_ = lean_ctor_get(v_p_u2082_480_, 2);
lean_inc_ref(v_p_503_);
lean_dec_ref_known(v_p_u2082_480_, 3);
v___x_504_ = lean_apply_6(v_h__4_484_, v_k_498_, v_v_499_, v_p_500_, v_k_501_, v_v_502_, v_p_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object* v_motive_505_, lean_object* v_p_u2081_506_, lean_object* v_p_u2082_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_, lean_object* v_h__3_510_, lean_object* v_h__4_511_){
_start:
{
if (lean_obj_tag(v_p_u2081_506_) == 0)
{
lean_dec(v_h__4_511_);
lean_dec(v_h__3_510_);
if (lean_obj_tag(v_p_u2082_507_) == 0)
{
lean_object* v_k_512_; lean_object* v_k_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_509_);
v_k_512_ = lean_ctor_get(v_p_u2081_506_, 0);
lean_inc(v_k_512_);
lean_dec_ref_known(v_p_u2081_506_, 1);
v_k_513_ = lean_ctor_get(v_p_u2082_507_, 0);
lean_inc(v_k_513_);
lean_dec_ref_known(v_p_u2082_507_, 1);
v___x_514_ = lean_apply_2(v_h__1_508_, v_k_512_, v_k_513_);
return v___x_514_;
}
else
{
lean_object* v_k_515_; lean_object* v_k_516_; lean_object* v_v_517_; lean_object* v_p_518_; lean_object* v___x_519_; 
lean_dec(v_h__1_508_);
v_k_515_ = lean_ctor_get(v_p_u2081_506_, 0);
lean_inc(v_k_515_);
lean_dec_ref_known(v_p_u2081_506_, 1);
v_k_516_ = lean_ctor_get(v_p_u2082_507_, 0);
lean_inc(v_k_516_);
v_v_517_ = lean_ctor_get(v_p_u2082_507_, 1);
lean_inc(v_v_517_);
v_p_518_ = lean_ctor_get(v_p_u2082_507_, 2);
lean_inc_ref(v_p_518_);
lean_dec_ref_known(v_p_u2082_507_, 3);
v___x_519_ = lean_apply_4(v_h__2_509_, v_k_515_, v_k_516_, v_v_517_, v_p_518_);
return v___x_519_;
}
}
else
{
lean_dec(v_h__2_509_);
lean_dec(v_h__1_508_);
if (lean_obj_tag(v_p_u2082_507_) == 0)
{
lean_object* v_k_520_; lean_object* v_v_521_; lean_object* v_p_522_; lean_object* v_k_523_; lean_object* v___x_524_; 
lean_dec(v_h__4_511_);
v_k_520_ = lean_ctor_get(v_p_u2081_506_, 0);
lean_inc(v_k_520_);
v_v_521_ = lean_ctor_get(v_p_u2081_506_, 1);
lean_inc(v_v_521_);
v_p_522_ = lean_ctor_get(v_p_u2081_506_, 2);
lean_inc_ref(v_p_522_);
lean_dec_ref_known(v_p_u2081_506_, 3);
v_k_523_ = lean_ctor_get(v_p_u2082_507_, 0);
lean_inc(v_k_523_);
lean_dec_ref_known(v_p_u2082_507_, 1);
v___x_524_ = lean_apply_4(v_h__3_510_, v_k_520_, v_v_521_, v_p_522_, v_k_523_);
return v___x_524_;
}
else
{
lean_object* v_k_525_; lean_object* v_v_526_; lean_object* v_p_527_; lean_object* v_k_528_; lean_object* v_v_529_; lean_object* v_p_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_510_);
v_k_525_ = lean_ctor_get(v_p_u2081_506_, 0);
lean_inc(v_k_525_);
v_v_526_ = lean_ctor_get(v_p_u2081_506_, 1);
lean_inc(v_v_526_);
v_p_527_ = lean_ctor_get(v_p_u2081_506_, 2);
lean_inc_ref(v_p_527_);
lean_dec_ref_known(v_p_u2081_506_, 3);
v_k_528_ = lean_ctor_get(v_p_u2082_507_, 0);
lean_inc(v_k_528_);
v_v_529_ = lean_ctor_get(v_p_u2082_507_, 1);
lean_inc(v_v_529_);
v_p_530_ = lean_ctor_get(v_p_u2082_507_, 2);
lean_inc_ref(v_p_530_);
lean_dec_ref_known(v_p_u2082_507_, 3);
v___x_531_ = lean_apply_6(v_h__4_511_, v_k_525_, v_v_526_, v_p_527_, v_k_528_, v_v_529_, v_p_530_);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t v_x_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_, lean_object* v_h__3_535_){
_start:
{
switch(v_x_532_)
{
case 0:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_h__2_534_);
lean_dec(v_h__1_533_);
v___x_536_ = lean_box(0);
v___x_537_ = lean_apply_1(v_h__3_535_, v___x_536_);
return v___x_537_;
}
case 1:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v_h__3_535_);
lean_dec(v_h__2_534_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_apply_1(v_h__1_533_, v___x_538_);
return v___x_539_;
}
default: 
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v_h__3_535_);
lean_dec(v_h__1_533_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_apply_1(v_h__2_534_, v___x_540_);
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object* v_x_542_, lean_object* v_h__1_543_, lean_object* v_h__2_544_, lean_object* v_h__3_545_){
_start:
{
uint8_t v_x_33__boxed_546_; lean_object* v_res_547_; 
v_x_33__boxed_546_ = lean_unbox(v_x_542_);
v_res_547_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_33__boxed_546_, v_h__1_543_, v_h__2_544_, v_h__3_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object* v_motive_548_, uint8_t v_x_549_, lean_object* v_h__1_550_, lean_object* v_h__2_551_, lean_object* v_h__3_552_){
_start:
{
switch(v_x_549_)
{
case 0:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_h__2_551_);
lean_dec(v_h__1_550_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v_h__3_552_, v___x_553_);
return v___x_554_;
}
case 1:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_apply_1(v_h__1_550_, v___x_555_);
return v___x_556_;
}
default: 
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_h__3_552_);
lean_dec(v_h__1_550_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v_h__2_551_, v___x_557_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_h__1_561_, lean_object* v_h__2_562_, lean_object* v_h__3_563_){
_start:
{
uint8_t v_x_48__boxed_564_; lean_object* v_res_565_; 
v_x_48__boxed_564_ = lean_unbox(v_x_560_);
v_res_565_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_559_, v_x_48__boxed_564_, v_h__1_561_, v_h__2_562_, v_h__3_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object* v_p_u2082_567_, lean_object* v_p_u2081_568_, lean_object* v_acc_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_toCold_582_; lean_object* v_options_583_; lean_object* v_currRecDepth_584_; lean_object* v_maxRecDepth_585_; lean_object* v_ref_586_; lean_object* v_currNamespace_587_; lean_object* v_openDecls_588_; lean_object* v_initHeartbeats_589_; lean_object* v_maxHeartbeats_590_; lean_object* v_currMacroScope_591_; uint8_t v_diag_592_; uint8_t v_suppressElabErrors_593_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_toCold_582_ = lean_ctor_get(v_a_579_, 0);
lean_inc_ref(v_toCold_582_);
v_options_583_ = lean_ctor_get(v_a_579_, 1);
lean_inc_ref(v_options_583_);
v_currRecDepth_584_ = lean_ctor_get(v_a_579_, 2);
lean_inc(v_currRecDepth_584_);
v_maxRecDepth_585_ = lean_ctor_get(v_a_579_, 3);
lean_inc(v_maxRecDepth_585_);
v_ref_586_ = lean_ctor_get(v_a_579_, 4);
lean_inc(v_ref_586_);
v_currNamespace_587_ = lean_ctor_get(v_a_579_, 5);
lean_inc(v_currNamespace_587_);
v_openDecls_588_ = lean_ctor_get(v_a_579_, 6);
lean_inc(v_openDecls_588_);
v_initHeartbeats_589_ = lean_ctor_get(v_a_579_, 7);
lean_inc(v_initHeartbeats_589_);
v_maxHeartbeats_590_ = lean_ctor_get(v_a_579_, 8);
lean_inc(v_maxHeartbeats_590_);
v_currMacroScope_591_ = lean_ctor_get(v_a_579_, 9);
lean_inc(v_currMacroScope_591_);
v_diag_592_ = lean_ctor_get_uint8(v_a_579_, sizeof(void*)*10);
v_suppressElabErrors_593_ = lean_ctor_get_uint8(v_a_579_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_579_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_eq(v_maxRecDepth_585_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_eq(v_currRecDepth_584_, v_maxRecDepth_585_);
if (v___x_622_ == 0)
{
goto v___jp_594_;
}
else
{
lean_object* v___x_623_; 
lean_dec(v_currMacroScope_591_);
lean_dec(v_maxHeartbeats_590_);
lean_dec(v_initHeartbeats_589_);
lean_dec(v_openDecls_588_);
lean_dec(v_currNamespace_587_);
lean_dec(v_maxRecDepth_585_);
lean_dec(v_currRecDepth_584_);
lean_dec_ref(v_options_583_);
lean_dec_ref(v_toCold_582_);
lean_dec_ref(v_acc_569_);
lean_dec_ref(v_p_u2081_568_);
lean_dec_ref(v_p_u2082_567_);
v___x_623_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_586_);
return v___x_623_;
}
}
else
{
goto v___jp_594_;
}
v___jp_594_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_currRecDepth_584_, v___x_595_);
lean_dec(v_currRecDepth_584_);
v___x_597_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_597_, 0, v_toCold_582_);
lean_ctor_set(v___x_597_, 1, v_options_583_);
lean_ctor_set(v___x_597_, 2, v___x_596_);
lean_ctor_set(v___x_597_, 3, v_maxRecDepth_585_);
lean_ctor_set(v___x_597_, 4, v_ref_586_);
lean_ctor_set(v___x_597_, 5, v_currNamespace_587_);
lean_ctor_set(v___x_597_, 6, v_openDecls_588_);
lean_ctor_set(v___x_597_, 7, v_initHeartbeats_589_);
lean_ctor_set(v___x_597_, 8, v_maxHeartbeats_590_);
lean_ctor_set(v___x_597_, 9, v_currMacroScope_591_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*10, v_diag_592_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*10 + 1, v_suppressElabErrors_593_);
if (lean_obj_tag(v_p_u2081_568_) == 0)
{
lean_object* v_k_598_; lean_object* v___x_599_; 
v_k_598_ = lean_ctor_get(v_p_u2081_568_, 0);
lean_inc(v_k_598_);
lean_dec_ref_known(v_p_u2081_568_, 1);
v___x_599_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_598_, v_p_u2082_567_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v___x_597_, v_a_580_);
lean_dec(v_k_598_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_569_, v_a_600_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v___x_597_, v_a_580_);
return v___x_601_;
}
else
{
lean_dec_ref_known(v___x_597_, 10);
lean_dec_ref(v_acc_569_);
return v___x_599_;
}
}
else
{
lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v_p_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_k_602_ = lean_ctor_get(v_p_u2081_568_, 0);
lean_inc(v_k_602_);
v_v_603_ = lean_ctor_get(v_p_u2081_568_, 1);
lean_inc(v_v_603_);
v_p_604_ = lean_ctor_get(v_p_u2081_568_, 2);
lean_inc_ref(v_p_604_);
lean_dec_ref_known(v_p_u2081_568_, 3);
v___x_605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
v___x_606_ = l_Lean_Core_checkSystem(v___x_605_, v___x_597_, v_a_580_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_607_; 
lean_dec_ref_known(v___x_606_, 1);
lean_inc_ref(v_p_u2082_567_);
v___x_607_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_602_, v_v_603_, v_p_u2082_567_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v___x_597_, v_a_580_);
lean_dec(v_k_602_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
lean_inc_ref(v___x_597_);
v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_569_, v_a_608_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v___x_597_, v_a_580_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v_p_u2081_568_ = v_p_604_;
v_acc_569_ = v_a_610_;
v_a_579_ = v___x_597_;
goto _start;
}
else
{
lean_dec_ref(v_p_604_);
lean_dec_ref_known(v___x_597_, 10);
lean_dec_ref(v_p_u2082_567_);
return v___x_609_;
}
}
else
{
lean_dec_ref(v_p_604_);
lean_dec_ref_known(v___x_597_, 10);
lean_dec_ref(v_acc_569_);
lean_dec_ref(v_p_u2082_567_);
return v___x_607_;
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_p_604_);
lean_dec(v_v_603_);
lean_dec(v_k_602_);
lean_dec_ref_known(v___x_597_, 10);
lean_dec_ref(v_acc_569_);
lean_dec_ref(v_p_u2082_567_);
v_a_612_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_606_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_606_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object* v_p_u2082_624_, lean_object* v_p_u2081_625_, lean_object* v_acc_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_624_, v_p_u2081_625_, v_acc_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object* v_p_u2081_642_, lean_object* v_p_u2082_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
lean_inc_ref(v_a_653_);
v___x_657_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_643_, v_p_u2081_642_, v___x_656_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object* v_p_u2081_658_, lean_object* v_p_u2082_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_658_, v_p_u2082_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_to_int(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object* v_p_677_, lean_object* v_k_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_toCold_691_; lean_object* v_options_692_; lean_object* v_currRecDepth_693_; lean_object* v_maxRecDepth_694_; lean_object* v_ref_695_; lean_object* v_currNamespace_696_; lean_object* v_openDecls_697_; lean_object* v_initHeartbeats_698_; lean_object* v_maxHeartbeats_699_; lean_object* v_currMacroScope_700_; uint8_t v_diag_701_; uint8_t v_suppressElabErrors_702_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_toCold_691_ = lean_ctor_get(v_a_688_, 0);
v_options_692_ = lean_ctor_get(v_a_688_, 1);
v_currRecDepth_693_ = lean_ctor_get(v_a_688_, 2);
v_maxRecDepth_694_ = lean_ctor_get(v_a_688_, 3);
v_ref_695_ = lean_ctor_get(v_a_688_, 4);
v_currNamespace_696_ = lean_ctor_get(v_a_688_, 5);
v_openDecls_697_ = lean_ctor_get(v_a_688_, 6);
v_initHeartbeats_698_ = lean_ctor_get(v_a_688_, 7);
v_maxHeartbeats_699_ = lean_ctor_get(v_a_688_, 8);
v_currMacroScope_700_ = lean_ctor_get(v_a_688_, 9);
v_diag_701_ = lean_ctor_get_uint8(v_a_688_, sizeof(void*)*10);
v_suppressElabErrors_702_ = lean_ctor_get_uint8(v_a_688_, sizeof(void*)*10 + 1);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_eq(v_maxRecDepth_694_, v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = lean_nat_dec_eq(v_currRecDepth_693_, v_maxRecDepth_694_);
if (v___x_725_ == 0)
{
goto v___jp_703_;
}
else
{
lean_object* v___x_726_; 
lean_dec_ref(v_p_677_);
lean_inc(v_ref_695_);
v___x_726_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_695_);
return v___x_726_;
}
}
else
{
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v_zero_704_; uint8_t v_isZero_705_; 
v_zero_704_ = lean_unsigned_to_nat(0u);
v_isZero_705_ = lean_nat_dec_eq(v_k_678_, v_zero_704_);
if (v_isZero_705_ == 1)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec_ref(v_p_677_);
v___x_706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
else
{
lean_object* v_one_708_; lean_object* v_n_709_; uint8_t v_isZero_710_; 
v_one_708_ = lean_unsigned_to_nat(1u);
v_n_709_ = lean_nat_sub(v_k_678_, v_one_708_);
v_isZero_710_ = lean_nat_dec_eq(v_n_709_, v_zero_704_);
if (v_isZero_710_ == 1)
{
lean_object* v___x_711_; 
lean_dec(v_n_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_p_677_);
return v___x_711_;
}
else
{
lean_object* v_n_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v_isZero_715_; 
v_n_712_ = lean_nat_sub(v_n_709_, v_one_708_);
lean_dec(v_n_709_);
v___x_713_ = lean_nat_add(v_currRecDepth_693_, v_one_708_);
lean_inc(v_currMacroScope_700_);
lean_inc(v_maxHeartbeats_699_);
lean_inc(v_initHeartbeats_698_);
lean_inc(v_openDecls_697_);
lean_inc(v_currNamespace_696_);
lean_inc(v_ref_695_);
lean_inc(v_maxRecDepth_694_);
lean_inc_ref(v_options_692_);
lean_inc_ref(v_toCold_691_);
v___x_714_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_714_, 0, v_toCold_691_);
lean_ctor_set(v___x_714_, 1, v_options_692_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
lean_ctor_set(v___x_714_, 3, v_maxRecDepth_694_);
lean_ctor_set(v___x_714_, 4, v_ref_695_);
lean_ctor_set(v___x_714_, 5, v_currNamespace_696_);
lean_ctor_set(v___x_714_, 6, v_openDecls_697_);
lean_ctor_set(v___x_714_, 7, v_initHeartbeats_698_);
lean_ctor_set(v___x_714_, 8, v_maxHeartbeats_699_);
lean_ctor_set(v___x_714_, 9, v_currMacroScope_700_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*10, v_diag_701_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*10 + 1, v_suppressElabErrors_702_);
v_isZero_715_ = lean_nat_dec_eq(v_n_712_, v_zero_704_);
if (v_isZero_715_ == 1)
{
lean_object* v___x_716_; 
lean_dec(v_n_712_);
lean_inc_ref(v_p_677_);
v___x_716_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_677_, v_p_677_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v___x_714_, v_a_689_);
lean_dec_ref_known(v___x_714_, 10);
return v___x_716_;
}
else
{
lean_object* v_n_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_n_717_ = lean_nat_sub(v_n_712_, v_one_708_);
lean_dec(v_n_712_);
v___x_718_ = lean_unsigned_to_nat(2u);
v___x_719_ = lean_nat_add(v_n_717_, v___x_718_);
lean_dec(v_n_717_);
lean_inc_ref(v_p_677_);
v___x_720_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_677_, v___x_719_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v___x_714_, v_a_689_);
lean_dec(v___x_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_677_, v_a_721_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v___x_714_, v_a_689_);
lean_dec_ref_known(v___x_714_, 10);
return v___x_722_;
}
else
{
lean_dec_ref_known(v___x_714_, 10);
lean_dec_ref(v_p_677_);
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object* v_p_727_, lean_object* v_k_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_727_, v_k_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_k_728_);
return v_res_741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_743_ = lean_int_neg(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object* v_e_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_n_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; 
switch(lean_obj_tag(v_e_746_))
{
case 1:
{
lean_object* v_k_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_817_; 
v_k_791_ = lean_ctor_get(v_e_746_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_e_746_);
if (v_isSharedCheck_817_ == 0)
{
v___x_793_ = v_e_746_;
v_isShared_794_ = v_isSharedCheck_817_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_k_791_);
lean_dec(v_e_746_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_817_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_nat_to_int(v_k_791_);
v___x_796_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_795_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_808_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_808_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_808_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_808_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 0);
lean_ctor_set(v___x_793_, 0, v_a_797_);
v___x_802_ = v___x_793_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_807_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_803_);
v___x_805_ = v___x_799_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_del_object(v___x_793_);
v_a_809_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_796_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_796_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
case 3:
{
lean_object* v_i_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_827_; 
v_i_818_ = lean_ctor_get(v_e_746_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_e_746_);
if (v_isSharedCheck_827_ == 0)
{
v___x_820_ = v_e_746_;
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_i_818_);
lean_dec(v_e_746_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
}
case 4:
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v_e_746_, 0);
lean_inc_ref(v_a_828_);
lean_dec_ref_known(v_e_746_, 1);
v___x_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_828_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
if (lean_obj_tag(v_a_830_) == 0)
{
return v___x_829_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref_known(v___x_829_, 1);
v_val_831_ = lean_ctor_get(v_a_830_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_a_830_);
if (v_isSharedCheck_856_ == 0)
{
v___x_833_ = v_a_830_;
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v_a_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_835_, v_val_831_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_847_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_a_837_);
v___x_842_ = v___x_833_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_del_object(v___x_833_);
v_a_848_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_836_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_836_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
else
{
return v___x_829_;
}
}
case 5:
{
lean_object* v_a_857_; lean_object* v_b_858_; lean_object* v___x_859_; 
v_a_857_ = lean_ctor_get(v_e_746_, 0);
lean_inc_ref(v_a_857_);
v_b_858_ = lean_ctor_get(v_e_746_, 1);
lean_inc_ref(v_b_858_);
lean_dec_ref_known(v_e_746_, 2);
v___x_859_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_857_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
if (lean_obj_tag(v_a_860_) == 0)
{
lean_dec_ref(v_b_858_);
return v___x_859_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_862_; 
lean_dec_ref_known(v___x_859_, 1);
v_val_861_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v_a_860_, 1);
v___x_862_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_858_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
if (lean_obj_tag(v_a_863_) == 0)
{
lean_dec(v_val_861_);
return v___x_862_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref_known(v___x_862_, 1);
v_val_864_ = lean_ctor_get(v_a_863_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_888_ == 0)
{
v___x_866_ = v_a_863_;
v_isShared_867_ = v_isSharedCheck_888_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v_a_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_888_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
lean_inc_ref(v_a_756_);
v___x_868_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_861_, v_val_864_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_879_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_879_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_a_869_);
v___x_874_ = v___x_866_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_878_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_del_object(v___x_866_);
v_a_880_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_868_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_868_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
else
{
lean_dec(v_val_861_);
return v___x_862_;
}
}
}
else
{
lean_dec_ref(v_b_858_);
return v___x_859_;
}
}
case 6:
{
lean_object* v_a_889_; lean_object* v_b_890_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v_e_746_, 0);
lean_inc_ref(v_a_889_);
v_b_890_ = lean_ctor_get(v_e_746_, 1);
lean_inc_ref(v_b_890_);
lean_dec_ref_known(v_e_746_, 2);
v___x_891_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_889_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
if (lean_obj_tag(v_a_892_) == 0)
{
lean_dec_ref(v_b_890_);
return v___x_891_;
}
else
{
lean_object* v_val_893_; lean_object* v___x_894_; 
lean_dec_ref_known(v___x_891_, 1);
v_val_893_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_a_892_, 1);
v___x_894_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_890_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
if (lean_obj_tag(v_a_895_) == 0)
{
lean_dec(v_val_893_);
return v___x_894_;
}
else
{
lean_object* v_val_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref_known(v___x_894_, 1);
v_val_896_ = lean_ctor_get(v_a_895_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_a_895_);
if (v_isSharedCheck_931_ == 0)
{
v___x_898_ = v_a_895_;
v_isShared_899_ = v_isSharedCheck_931_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_val_896_);
lean_dec(v_a_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_931_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_900_, v_val_896_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
lean_inc_ref(v_a_756_);
v___x_903_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_893_, v_a_902_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v_a_904_);
v___x_909_ = v___x_898_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_del_object(v___x_898_);
v_a_915_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_903_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_903_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_898_);
lean_dec(v_val_893_);
v_a_923_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_901_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_901_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
else
{
lean_dec(v_val_893_);
return v___x_894_;
}
}
}
else
{
lean_dec_ref(v_b_890_);
return v___x_891_;
}
}
case 7:
{
lean_object* v_a_932_; lean_object* v_b_933_; lean_object* v___x_934_; 
v_a_932_ = lean_ctor_get(v_e_746_, 0);
lean_inc_ref(v_a_932_);
v_b_933_ = lean_ctor_get(v_e_746_, 1);
lean_inc_ref(v_b_933_);
lean_dec_ref_known(v_e_746_, 2);
v___x_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_932_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
if (lean_obj_tag(v_a_935_) == 0)
{
lean_dec_ref(v_b_933_);
return v___x_934_;
}
else
{
lean_object* v_val_936_; lean_object* v___x_937_; 
lean_dec_ref_known(v___x_934_, 1);
v_val_936_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v_a_935_, 1);
v___x_937_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_933_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
if (lean_obj_tag(v_a_938_) == 0)
{
lean_dec(v_val_936_);
return v___x_937_;
}
else
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref_known(v___x_937_, 1);
v_val_939_ = lean_ctor_get(v_a_938_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_938_);
if (v_isSharedCheck_963_ == 0)
{
v___x_941_ = v_a_938_;
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v_a_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; 
v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_val_936_, v_val_939_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_954_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_954_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_a_944_);
v___x_949_ = v___x_941_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_941_);
v_a_955_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_943_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_943_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
else
{
lean_dec(v_val_936_);
return v___x_937_;
}
}
}
else
{
lean_dec_ref(v_b_933_);
return v___x_934_;
}
}
case 8:
{
lean_object* v_a_964_; lean_object* v_k_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1067_; 
v_a_964_ = lean_ctor_get(v_e_746_, 0);
v_k_965_ = lean_ctor_get(v_e_746_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_e_746_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_967_ = v_e_746_;
v_isShared_968_ = v_isSharedCheck_1067_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_k_965_);
lean_inc(v_a_964_);
lean_dec(v_e_746_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1067_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_nat_dec_eq(v_k_965_, v___x_969_);
if (v___x_970_ == 0)
{
switch(lean_obj_tag(v_a_964_))
{
case 0:
{
lean_object* v_k_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1022_; 
lean_del_object(v___x_967_);
v_k_971_ = lean_ctor_get(v_a_964_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_973_ = v_a_964_;
v_isShared_974_ = v_isSharedCheck_1022_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_k_971_);
lean_dec(v_a_964_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1022_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; 
lean_inc(v_k_965_);
v___x_975_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_k_965_, v_a_750_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1013_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1013_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1013_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
if (lean_obj_tag(v_a_976_) == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_del_object(v___x_973_);
lean_dec(v_k_971_);
lean_dec(v_k_965_);
v___x_980_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1011_; 
lean_del_object(v___x_978_);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_a_976_, 0);
lean_dec(v_unused_1012_);
v___x_985_ = v_a_976_;
v_isShared_986_ = v_isSharedCheck_1011_;
goto v_resetjp_984_;
}
else
{
lean_dec(v_a_976_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1011_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_Int_pow(v_k_971_, v_k_965_);
lean_dec(v_k_965_);
lean_dec(v_k_971_);
v___x_988_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_987_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_a_989_);
v___x_994_ = v___x_973_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_1001_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_994_);
v___x_996_ = v___x_985_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_996_);
v___x_998_ = v___x_991_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_985_);
lean_del_object(v___x_973_);
v_a_1003_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_988_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_988_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_del_object(v___x_973_);
lean_dec(v_k_971_);
lean_dec(v_k_965_);
v_a_1014_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_975_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_975_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
v_i_1023_ = lean_ctor_get(v_a_964_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v_a_964_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_i_1023_);
lean_dec(v_a_964_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 0);
lean_ctor_set(v___x_967_, 0, v_i_1023_);
v___x_1028_ = v___x_967_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_i_1023_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_k_965_);
v___x_1028_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_1030_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1031_);
v___x_1033_ = v___x_1025_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
}
default: 
{
lean_object* v___x_1038_; 
lean_del_object(v___x_967_);
v___x_1038_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_964_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
if (lean_obj_tag(v_a_1039_) == 0)
{
lean_dec(v_k_965_);
return v___x_1038_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref_known(v___x_1038_, 1);
v_val_1040_ = lean_ctor_get(v_a_1039_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_1039_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1042_ = v_a_1039_;
v_isShared_1043_ = v_isSharedCheck_1064_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v_a_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1064_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_1040_, v_k_965_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_k_965_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1055_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_a_1045_);
v___x_1050_ = v___x_1042_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1050_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
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
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_1042_);
v_a_1056_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1044_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1044_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
else
{
lean_dec(v_k_965_);
return v___x_1038_;
}
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_967_);
lean_dec(v_k_965_);
lean_dec_ref(v_a_964_);
v___x_1065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
default: 
{
lean_object* v_k_1068_; 
v_k_1068_ = lean_ctor_get(v_e_746_, 0);
lean_inc(v_k_1068_);
lean_dec_ref(v_e_746_);
v_n_760_ = v_k_1068_;
v___y_761_ = v_a_747_;
v___y_762_ = v_a_748_;
v___y_763_ = v_a_749_;
v___y_764_ = v_a_750_;
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
v___y_767_ = v_a_753_;
v___y_768_ = v_a_754_;
v___y_769_ = v_a_755_;
v___y_770_ = v_a_756_;
v___y_771_ = v_a_757_;
goto v___jp_759_;
}
}
v___jp_759_:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_n_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_782_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v_a_773_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_778_);
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_772_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_772_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object* v_e_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_1111_, lean_object* v_k_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1112_, v_p_1111_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_1126_, lean_object* v_k_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1126_, v_k_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_k_1127_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_1141_, lean_object* v_k_1142_, lean_object* v_m_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1142_, v_m_1143_, v_p_1141_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_1157_, lean_object* v_k_1158_, lean_object* v_m_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1157_, v_k_1158_, v_m_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_k_1158_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_1173_, lean_object* v_p_u2082_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_1173_, v_p_u2082_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_1188_, lean_object* v_p_u2082_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_1188_, v_p_u2082_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_1203_, lean_object* v_p_u2082_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; 
lean_inc_ref(v_a_1214_);
v___x_1217_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_1203_, v_p_u2082_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1218_, lean_object* v_p_u2082_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1218_, v_p_u2082_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
v___x_1236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1234_);
lean_ctor_set(v___x_1236_, 2, v___x_1233_);
lean_ctor_set(v___x_1236_, 3, v___x_1234_);
lean_ctor_set(v___x_1236_, 4, v___x_1233_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1237_, lean_object* v_p_u2082_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
if (lean_obj_tag(v_p_u2081_1237_) == 1)
{
if (lean_obj_tag(v_p_u2082_1238_) == 1)
{
lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_p_1256_; lean_object* v_k_1257_; lean_object* v_v_1258_; lean_object* v_p_1259_; lean_object* v_m_1260_; lean_object* v_m_u2081_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_g_1264_; lean_object* v___x_1265_; lean_object* v_c_u2081_1266_; lean_object* v___x_1267_; 
v_k_1254_ = lean_ctor_get(v_p_u2081_1237_, 0);
lean_inc(v_k_1254_);
v_v_1255_ = lean_ctor_get(v_p_u2081_1237_, 1);
lean_inc_n(v_v_1255_, 2);
v_p_1256_ = lean_ctor_get(v_p_u2081_1237_, 2);
lean_inc_ref(v_p_1256_);
lean_dec_ref_known(v_p_u2081_1237_, 3);
v_k_1257_ = lean_ctor_get(v_p_u2082_1238_, 0);
lean_inc(v_k_1257_);
v_v_1258_ = lean_ctor_get(v_p_u2082_1238_, 1);
lean_inc_n(v_v_1258_, 2);
v_p_1259_ = lean_ctor_get(v_p_u2082_1238_, 2);
lean_inc_ref(v_p_1259_);
lean_dec_ref_known(v_p_u2082_1238_, 3);
v_m_1260_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1255_, v_v_1258_);
lean_inc(v_m_1260_);
v_m_u2081_1261_ = l_Lean_Grind_CommRing_Mon_div(v_m_1260_, v_v_1255_);
v___x_1262_ = lean_nat_abs(v_k_1254_);
v___x_1263_ = lean_nat_abs(v_k_1257_);
v_g_1264_ = lean_nat_gcd(v___x_1262_, v___x_1263_);
lean_dec(v___x_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_nat_to_int(v_g_1264_);
v_c_u2081_1266_ = lean_int_ediv(v_k_1257_, v___x_1265_);
lean_dec(v_k_1257_);
lean_inc(v_m_u2081_1261_);
v___x_1267_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_1266_, v_m_u2081_1261_, v_p_1256_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_m_u2082_1269_; lean_object* v___x_1270_; lean_object* v_c_u2082_1271_; lean_object* v___x_1272_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v_m_u2082_1269_ = l_Lean_Grind_CommRing_Mon_div(v_m_1260_, v_v_1258_);
v___x_1270_ = lean_int_neg(v_k_1254_);
lean_dec(v_k_1254_);
v_c_u2082_1271_ = lean_int_ediv(v___x_1270_, v___x_1265_);
lean_dec(v___x_1265_);
lean_dec(v___x_1270_);
lean_inc(v_m_u2082_1269_);
v___x_1272_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_1271_, v_m_u2082_1269_, v_p_1259_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
lean_inc_ref(v_a_1248_);
v___x_1274_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1268_, v_a_1273_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1283_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1279_, 0, v_a_1275_);
lean_ctor_set(v___x_1279_, 1, v_c_u2081_1266_);
lean_ctor_set(v___x_1279_, 2, v_m_u2081_1261_);
lean_ctor_set(v___x_1279_, 3, v_c_u2082_1271_);
lean_ctor_set(v___x_1279_, 4, v_m_u2082_1269_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_c_u2082_1271_);
lean_dec(v_m_u2082_1269_);
lean_dec(v_c_u2081_1266_);
lean_dec(v_m_u2081_1261_);
v_a_1284_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1274_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_c_u2082_1271_);
lean_dec(v_m_u2082_1269_);
lean_dec(v_a_1268_);
lean_dec(v_c_u2081_1266_);
lean_dec(v_m_u2081_1261_);
v_a_1292_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1272_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1272_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_c_u2081_1266_);
lean_dec(v___x_1265_);
lean_dec(v_m_u2081_1261_);
lean_dec(v_m_1260_);
lean_dec_ref(v_p_1259_);
lean_dec(v_v_1258_);
lean_dec(v_k_1254_);
v_a_1300_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1267_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1267_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_dec_ref_known(v_p_u2081_1237_, 3);
lean_dec_ref(v_p_u2082_1238_);
goto v___jp_1251_;
}
}
else
{
lean_dec_ref(v_p_u2082_1238_);
lean_dec_ref(v_p_u2081_1237_);
goto v___jp_1251_;
}
v___jp_1251_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1308_, lean_object* v_p_u2082_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1308_, v_p_u2082_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
if (lean_obj_tag(v_m_1333_) == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
else
{
lean_object* v_p_1348_; lean_object* v_m_1349_; lean_object* v___x_1350_; 
v_p_1348_ = lean_ctor_get(v_m_1333_, 0);
lean_inc_ref(v_p_1348_);
v_m_1349_ = lean_ctor_get(v_m_1333_, 1);
lean_inc(v_m_1349_);
lean_dec_ref_known(v_m_1333_, 2);
v___x_1350_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_toRing_1352_; lean_object* v_vars_1353_; lean_object* v_x_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1422_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v_toRing_1352_ = lean_ctor_get(v_a_1351_, 0);
lean_inc_ref(v_toRing_1352_);
lean_dec(v_a_1351_);
v_vars_1353_ = lean_ctor_get(v_toRing_1352_, 14);
lean_inc_ref(v_vars_1353_);
lean_dec_ref(v_toRing_1352_);
v_x_1354_ = lean_ctor_get(v_p_1348_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_p_1348_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v_p_1348_, 1);
lean_dec(v_unused_1423_);
v___x_1356_ = v_p_1348_;
v_isShared_1357_ = v_isSharedCheck_1422_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_x_1354_);
lean_dec(v_p_1348_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1422_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___y_1359_; lean_object* v_size_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_size_1417_ = lean_ctor_get(v_vars_1353_, 2);
v___x_1418_ = l_Lean_instInhabitedExpr;
v___x_1419_ = lean_nat_dec_lt(v_x_1354_, v_size_1417_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec_ref(v_vars_1353_);
v___x_1420_ = l_outOfBounds___redArg(v___x_1418_);
v___y_1359_ = v___x_1420_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1418_, v_vars_1353_, v_x_1354_);
lean_dec_ref(v_vars_1353_);
v___y_1359_ = v___x_1421_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = l_Lean_Expr_cleanupAnnotations(v___y_1359_);
v___x_1361_ = l_Lean_Expr_isApp(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v___x_1360_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v_arg_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_arg_1363_ = lean_ctor_get(v___x_1360_, 1);
lean_inc_ref(v_arg_1363_);
v___x_1364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1360_);
v___x_1365_ = l_Lean_Expr_isApp(v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v_arg_1363_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1364_);
v___x_1368_ = l_Lean_Expr_isApp(v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v___x_1367_);
lean_dec_ref(v_arg_1363_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1367_);
v___x_1371_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
v___x_1372_ = l_Lean_Expr_isConstOf(v___x_1370_, v___x_1371_);
lean_dec_ref(v___x_1370_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v_arg_1363_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = l_Lean_Expr_cleanupAnnotations(v_arg_1363_);
v___x_1375_ = l_Lean_Expr_isApp(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec_ref(v___x_1374_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1374_);
v___x_1378_ = l_Lean_Expr_isApp(v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v___x_1377_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v_arg_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_arg_1380_ = lean_ctor_get(v___x_1377_, 1);
lean_inc_ref(v_arg_1380_);
v___x_1381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1377_);
v___x_1382_ = l_Lean_Expr_isApp(v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v___x_1381_);
lean_dec_ref(v_arg_1380_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1381_);
v___x_1385_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
v___x_1386_ = l_Lean_Expr_isConstOf(v___x_1384_, v___x_1385_);
lean_dec_ref(v___x_1384_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v_arg_1380_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
else
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Meta_getNatValue_x3f(v_arg_1380_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v_arg_1380_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1408_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1408_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1408_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
if (lean_obj_tag(v_a_1389_) == 1)
{
lean_object* v_val_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_m_1349_);
v_val_1393_ = lean_ctor_get(v_a_1389_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_a_1389_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1395_ = v_a_1389_;
v_isShared_1396_ = v_isSharedCheck_1406_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_val_1393_);
lean_dec(v_a_1389_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1406_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_x_1354_);
lean_ctor_set(v___x_1356_, 0, v_val_1393_);
v___x_1398_ = v___x_1356_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_val_1393_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_x_1354_);
v___x_1398_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1398_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1400_);
v___x_1402_ = v___x_1391_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
else
{
lean_del_object(v___x_1391_);
lean_dec(v_a_1389_);
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
v_m_1333_ = v_m_1349_;
goto _start;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1356_);
lean_dec(v_x_1354_);
lean_dec(v_m_1349_);
v_a_1409_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1388_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1388_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
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
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_m_1349_);
lean_dec_ref(v_p_1348_);
v_a_1424_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1350_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1350_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
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
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
if (lean_obj_tag(v_p_1446_) == 0)
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_isSharedCheck_1466_ = !lean_is_exclusive(v_p_1446_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_p_1446_, 0);
lean_dec(v_unused_1467_);
v___x_1460_ = v_p_1446_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_p_1446_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_v_1468_; lean_object* v_p_1469_; lean_object* v___x_1470_; 
v_v_1468_ = lean_ctor_get(v_p_1446_, 1);
lean_inc(v_v_1468_);
v_p_1469_ = lean_ctor_get(v_p_1446_, 2);
lean_inc_ref(v_p_1469_);
lean_dec_ref_known(v_p_1446_, 3);
v___x_1470_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_v_1468_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_dec_ref_known(v_a_1471_, 1);
lean_dec_ref(v_p_1469_);
return v___x_1470_;
}
else
{
lean_dec(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v_p_1446_ = v_p_1469_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1469_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object* v_k_u2082_x27_1487_, lean_object* v_m_u2082_1488_, lean_object* v_p_u2082_1489_, uint8_t v_checkCoeff_1490_, lean_object* v_p_u2081_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
if (lean_obj_tag(v_p_u2081_1491_) == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref_known(v_p_u2081_1491_, 1);
lean_dec_ref(v_p_u2082_1489_);
lean_dec(v_m_u2082_1488_);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
else
{
lean_object* v_k_1506_; lean_object* v_v_1507_; lean_object* v_p_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1649_; 
v_k_1506_ = lean_ctor_get(v_p_u2081_1491_, 0);
v_v_1507_ = lean_ctor_get(v_p_u2081_1491_, 1);
v_p_1508_ = lean_ctor_get(v_p_u2081_1491_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_p_u2081_1491_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1510_ = v_p_u2081_1491_;
v_isShared_1511_ = v_isSharedCheck_1649_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_p_1508_);
lean_inc(v_v_1507_);
lean_inc(v_k_1506_);
lean_dec(v_p_u2081_1491_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1649_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
uint8_t v___y_1513_; uint8_t v___x_1645_; 
v___x_1645_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_1488_, v_v_1507_);
if (v___x_1645_ == 0)
{
v___y_1513_ = v___x_1645_;
goto v___jp_1512_;
}
else
{
if (v_checkCoeff_1490_ == 0)
{
v___y_1513_ = v___x_1645_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1646_ = lean_int_emod(v_k_1506_, v_k_u2082_x27_1487_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1648_ = lean_int_dec_eq(v___x_1646_, v___x_1647_);
lean_dec(v___x_1646_);
v___y_1513_ = v___x_1648_;
goto v___jp_1512_;
}
}
v___jp_1512_:
{
if (v___y_1513_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1487_, v_m_u2082_1488_, v_p_u2082_1489_, v_checkCoeff_1490_, v_p_1508_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1597_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1597_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1597_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
if (lean_obj_tag(v_a_1515_) == 1)
{
lean_object* v_val_1519_; lean_object* v___x_1520_; 
lean_del_object(v___x_1517_);
v_val_1519_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_val_1519_);
v___x_1520_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1584_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1584_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1584_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
if (lean_obj_tag(v_a_1521_) == 1)
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1557_; 
v_val_1525_ = lean_ctor_get(v_a_1521_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_a_1521_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1527_ = v_a_1521_;
v_isShared_1528_ = v_isSharedCheck_1557_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v_a_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1557_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_p_1529_; lean_object* v_k_u2081_1530_; lean_object* v_k_u2082_1531_; lean_object* v_m_u2082_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1556_; 
v_p_1529_ = lean_ctor_get(v_val_1519_, 0);
v_k_u2081_1530_ = lean_ctor_get(v_val_1519_, 1);
v_k_u2082_1531_ = lean_ctor_get(v_val_1519_, 2);
v_m_u2082_1532_ = lean_ctor_get(v_val_1519_, 3);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_val_1519_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1534_ = v_val_1519_;
v_isShared_1535_ = v_isSharedCheck_1556_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_m_u2082_1532_);
lean_inc(v_k_u2082_1531_);
lean_inc(v_k_u2081_1530_);
lean_inc(v_p_1529_);
lean_dec(v_val_1519_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1556_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1536_ = lean_int_mul(v_k_1506_, v_k_u2081_1530_);
lean_dec(v_k_1506_);
v___x_1537_ = lean_nat_to_int(v_val_1525_);
v___x_1538_ = lean_int_emod(v___x_1536_, v___x_1537_);
lean_dec(v___x_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1540_ = lean_int_dec_eq(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref_known(v_a_1515_, 1);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 2, v_p_1529_);
lean_ctor_set(v___x_1510_, 0, v___x_1538_);
v___x_1542_ = v___x_1510_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_v_1507_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_p_1529_);
v___x_1542_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1542_);
v___x_1544_ = v___x_1534_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_k_u2081_1530_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_k_u2082_1531_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_m_u2082_1532_);
v___x_1544_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1544_);
v___x_1546_ = v___x_1527_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1546_);
v___x_1548_ = v___x_1523_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
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
else
{
lean_object* v___x_1554_; 
lean_dec(v___x_1538_);
lean_del_object(v___x_1534_);
lean_dec(v_m_u2082_1532_);
lean_dec(v_k_u2082_1531_);
lean_dec(v_k_u2081_1530_);
lean_dec_ref(v_p_1529_);
lean_del_object(v___x_1527_);
lean_del_object(v___x_1510_);
lean_dec(v_v_1507_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_a_1515_);
v___x_1554_ = v___x_1523_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1515_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
else
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_a_1521_);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_a_1515_, 0);
lean_dec(v_unused_1583_);
v___x_1559_ = v_a_1515_;
v_isShared_1560_ = v_isSharedCheck_1582_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_a_1515_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1582_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_p_1561_; lean_object* v_k_u2081_1562_; lean_object* v_k_u2082_1563_; lean_object* v_m_u2082_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1581_; 
v_p_1561_ = lean_ctor_get(v_val_1519_, 0);
v_k_u2081_1562_ = lean_ctor_get(v_val_1519_, 1);
v_k_u2082_1563_ = lean_ctor_get(v_val_1519_, 2);
v_m_u2082_1564_ = lean_ctor_get(v_val_1519_, 3);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_val_1519_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1566_ = v_val_1519_;
v_isShared_1567_ = v_isSharedCheck_1581_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_m_u2082_1564_);
lean_inc(v_k_u2082_1563_);
lean_inc(v_k_u2081_1562_);
lean_inc(v_p_1561_);
lean_dec(v_val_1519_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1581_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_int_mul(v_k_1506_, v_k_u2081_1562_);
lean_dec(v_k_1506_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 2, v_p_1561_);
lean_ctor_set(v___x_1510_, 0, v___x_1568_);
v___x_1570_ = v___x_1510_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_v_1507_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_p_1561_);
v___x_1570_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1570_);
v___x_1572_ = v___x_1566_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_u2081_1562_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_k_u2082_1563_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_m_u2082_1564_);
v___x_1572_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1574_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1572_);
v___x_1574_ = v___x_1559_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1574_);
v___x_1576_ = v___x_1523_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
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
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_val_1519_);
lean_dec_ref_known(v_a_1515_, 1);
lean_del_object(v___x_1510_);
lean_dec(v_v_1507_);
lean_dec(v_k_1506_);
v_a_1585_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1520_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1520_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec(v_a_1515_);
lean_del_object(v___x_1510_);
lean_dec(v_v_1507_);
lean_dec(v_k_1506_);
v___x_1593_ = lean_box(0);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1593_);
v___x_1595_ = v___x_1517_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_del_object(v___x_1510_);
lean_dec(v_v_1507_);
lean_dec(v_k_1506_);
return v___x_1514_;
}
}
else
{
lean_object* v_m_u2082_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_g_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v_k_u2082_1604_; lean_object* v___x_1605_; 
lean_del_object(v___x_1510_);
v_m_u2082_1598_ = l_Lean_Grind_CommRing_Mon_div(v_v_1507_, v_m_u2082_1488_);
v___x_1599_ = lean_nat_abs(v_k_1506_);
v___x_1600_ = lean_nat_abs(v_k_u2082_x27_1487_);
v_g_1601_ = lean_nat_gcd(v___x_1599_, v___x_1600_);
lean_dec(v___x_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_nat_to_int(v_g_1601_);
v___x_1603_ = lean_int_neg(v_k_1506_);
lean_dec(v_k_1506_);
v_k_u2082_1604_ = lean_int_ediv(v___x_1603_, v___x_1602_);
lean_dec(v___x_1603_);
lean_inc(v_m_u2082_1598_);
v___x_1605_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_u2082_1604_, v_m_u2082_1598_, v_p_u2082_1489_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v_k_u2081_1607_; lean_object* v___x_1608_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v_k_u2081_1607_ = lean_int_ediv(v_k_u2082_x27_1487_, v___x_1602_);
lean_dec(v___x_1602_);
v___x_1608_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_u2081_1607_, v_p_1508_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
lean_inc_ref(v_a_1501_);
v___x_1610_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1606_, v_a_1609_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1615_, 0, v_a_1611_);
lean_ctor_set(v___x_1615_, 1, v_k_u2081_1607_);
lean_ctor_set(v___x_1615_, 2, v_k_u2082_1604_);
lean_ctor_set(v___x_1615_, 3, v_m_u2082_1598_);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_k_u2081_1607_);
lean_dec(v_k_u2082_1604_);
lean_dec(v_m_u2082_1598_);
v_a_1621_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1610_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1610_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_k_u2081_1607_);
lean_dec(v_a_1606_);
lean_dec(v_k_u2082_1604_);
lean_dec(v_m_u2082_1598_);
v_a_1629_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1608_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1608_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_k_u2082_1604_);
lean_dec(v___x_1602_);
lean_dec(v_m_u2082_1598_);
lean_dec_ref(v_p_1508_);
v_a_1637_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1605_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1605_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
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
lean_object* v_k_u2082_x27_1650_ = _args[0];
lean_object* v_m_u2082_1651_ = _args[1];
lean_object* v_p_u2082_1652_ = _args[2];
lean_object* v_checkCoeff_1653_ = _args[3];
lean_object* v_p_u2081_1654_ = _args[4];
lean_object* v_a_1655_ = _args[5];
lean_object* v_a_1656_ = _args[6];
lean_object* v_a_1657_ = _args[7];
lean_object* v_a_1658_ = _args[8];
lean_object* v_a_1659_ = _args[9];
lean_object* v_a_1660_ = _args[10];
lean_object* v_a_1661_ = _args[11];
lean_object* v_a_1662_ = _args[12];
lean_object* v_a_1663_ = _args[13];
lean_object* v_a_1664_ = _args[14];
lean_object* v_a_1665_ = _args[15];
lean_object* v_a_1666_ = _args[16];
_start:
{
uint8_t v_checkCoeff_boxed_1667_; lean_object* v_res_1668_; 
v_checkCoeff_boxed_1667_ = lean_unbox(v_checkCoeff_1653_);
v_res_1668_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1650_, v_m_u2082_1651_, v_p_u2082_1652_, v_checkCoeff_boxed_1667_, v_p_u2081_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_k_u2082_x27_1650_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object* v_p_u2081_1669_, lean_object* v_p_u2082_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
if (lean_obj_tag(v_p_u2082_1670_) == 1)
{
lean_object* v_k_1683_; lean_object* v_v_1684_; lean_object* v_p_1685_; lean_object* v___x_1686_; 
v_k_1683_ = lean_ctor_get(v_p_u2082_1670_, 0);
lean_inc(v_k_1683_);
v_v_1684_ = lean_ctor_get(v_p_u2082_1670_, 1);
lean_inc(v_v_1684_);
v_p_1685_ = lean_ctor_get(v_p_u2082_1670_, 2);
lean_inc_ref(v_p_1685_);
lean_dec_ref_known(v_p_u2082_1670_, 3);
v___x_1686_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_1671_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1688_) == 0)
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_unbox(v_a_1687_);
if (v___x_1689_ == 0)
{
uint8_t v___x_1690_; lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
v___x_1691_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1683_, v_v_1684_, v_p_1685_, v___x_1690_, v_p_u2081_1669_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_k_1683_);
return v___x_1691_;
}
else
{
lean_object* v_a_1692_; uint8_t v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1693_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
if (v___x_1693_ == 0)
{
uint8_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
v___x_1695_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1683_, v_v_1684_, v_p_1685_, v___x_1694_, v_p_u2081_1669_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_k_1683_);
return v___x_1695_;
}
else
{
uint8_t v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_a_1687_);
v___x_1696_ = 0;
v___x_1697_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1683_, v_v_1684_, v_p_1685_, v___x_1696_, v_p_u2081_1669_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_k_1683_);
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_a_1687_);
lean_dec_ref(v_p_1685_);
lean_dec(v_v_1684_);
lean_dec(v_k_1683_);
lean_dec_ref(v_p_u2081_1669_);
v_a_1698_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1688_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1688_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_p_1685_);
lean_dec(v_v_1684_);
lean_dec(v_k_1683_);
lean_dec_ref(v_p_u2081_1669_);
v_a_1706_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1686_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1686_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v_p_u2082_1670_);
lean_dec_ref(v_p_u2081_1669_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object* v_p_u2081_1716_, lean_object* v_p_u2082_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(v_p_u2081_1716_, v_p_u2082_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1730_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
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
