// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM public import Lean.Meta.Sym.Arith.Poly import Lean.Meta.Tactic.Grind.Arith.EvalNum import Init.Data.Nat.Linear
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
uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_75_);
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
lean_dec_ref(v_a_126_);
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
lean_dec_ref(v_a_178_);
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
lean_dec_ref(v_a_231_);
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
lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_options_337_; lean_object* v_currRecDepth_338_; lean_object* v_maxRecDepth_339_; lean_object* v_ref_340_; lean_object* v_currNamespace_341_; lean_object* v_openDecls_342_; lean_object* v_initHeartbeats_343_; lean_object* v_maxHeartbeats_344_; lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; uint8_t v_diag_347_; lean_object* v_cancelTk_x3f_348_; uint8_t v_suppressElabErrors_349_; lean_object* v_inheritedTraceOptions_350_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_fileName_335_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_fileName_335_);
v_fileMap_336_ = lean_ctor_get(v_a_332_, 1);
lean_inc_ref(v_fileMap_336_);
v_options_337_ = lean_ctor_get(v_a_332_, 2);
lean_inc_ref(v_options_337_);
v_currRecDepth_338_ = lean_ctor_get(v_a_332_, 3);
lean_inc(v_currRecDepth_338_);
v_maxRecDepth_339_ = lean_ctor_get(v_a_332_, 4);
lean_inc(v_maxRecDepth_339_);
v_ref_340_ = lean_ctor_get(v_a_332_, 5);
lean_inc(v_ref_340_);
v_currNamespace_341_ = lean_ctor_get(v_a_332_, 6);
lean_inc(v_currNamespace_341_);
v_openDecls_342_ = lean_ctor_get(v_a_332_, 7);
lean_inc(v_openDecls_342_);
v_initHeartbeats_343_ = lean_ctor_get(v_a_332_, 8);
lean_inc(v_initHeartbeats_343_);
v_maxHeartbeats_344_ = lean_ctor_get(v_a_332_, 9);
lean_inc(v_maxHeartbeats_344_);
v_quotContext_345_ = lean_ctor_get(v_a_332_, 10);
lean_inc(v_quotContext_345_);
v_currMacroScope_346_ = lean_ctor_get(v_a_332_, 11);
lean_inc(v_currMacroScope_346_);
v_diag_347_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14);
v_cancelTk_x3f_348_ = lean_ctor_get(v_a_332_, 12);
lean_inc(v_cancelTk_x3f_348_);
v_suppressElabErrors_349_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_350_ = lean_ctor_get(v_a_332_, 13);
lean_inc_ref(v_inheritedTraceOptions_350_);
lean_dec_ref(v_a_332_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_dec_eq(v_maxRecDepth_339_, v___x_464_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = lean_nat_dec_eq(v_currRecDepth_338_, v_maxRecDepth_339_);
if (v___x_466_ == 0)
{
goto v___jp_351_;
}
else
{
lean_object* v___x_467_; 
lean_dec_ref(v_inheritedTraceOptions_350_);
lean_dec(v_cancelTk_x3f_348_);
lean_dec(v_currMacroScope_346_);
lean_dec(v_quotContext_345_);
lean_dec(v_maxHeartbeats_344_);
lean_dec(v_initHeartbeats_343_);
lean_dec(v_openDecls_342_);
lean_dec(v_currNamespace_341_);
lean_dec(v_maxRecDepth_339_);
lean_dec(v_currRecDepth_338_);
lean_dec_ref(v_options_337_);
lean_dec_ref(v_fileMap_336_);
lean_dec_ref(v_fileName_335_);
lean_dec_ref(v_p_u2082_322_);
lean_dec_ref(v_p_u2081_321_);
v___x_467_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_340_);
return v___x_467_;
}
}
else
{
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_currRecDepth_338_, v___x_352_);
lean_dec(v_currRecDepth_338_);
v___x_354_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_354_, 0, v_fileName_335_);
lean_ctor_set(v___x_354_, 1, v_fileMap_336_);
lean_ctor_set(v___x_354_, 2, v_options_337_);
lean_ctor_set(v___x_354_, 3, v___x_353_);
lean_ctor_set(v___x_354_, 4, v_maxRecDepth_339_);
lean_ctor_set(v___x_354_, 5, v_ref_340_);
lean_ctor_set(v___x_354_, 6, v_currNamespace_341_);
lean_ctor_set(v___x_354_, 7, v_openDecls_342_);
lean_ctor_set(v___x_354_, 8, v_initHeartbeats_343_);
lean_ctor_set(v___x_354_, 9, v_maxHeartbeats_344_);
lean_ctor_set(v___x_354_, 10, v_quotContext_345_);
lean_ctor_set(v___x_354_, 11, v_currMacroScope_346_);
lean_ctor_set(v___x_354_, 12, v_cancelTk_x3f_348_);
lean_ctor_set(v___x_354_, 13, v_inheritedTraceOptions_350_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*14, v_diag_347_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*14 + 1, v_suppressElabErrors_349_);
if (lean_obj_tag(v_p_u2081_321_) == 0)
{
if (lean_obj_tag(v_p_u2082_322_) == 0)
{
lean_object* v_k_355_; lean_object* v_k_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_381_; 
v_k_355_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_inc(v_k_355_);
lean_dec_ref(v_p_u2081_321_);
v_k_356_ = lean_ctor_get(v_p_u2082_322_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_381_ == 0)
{
v___x_358_ = v_p_u2082_322_;
v_isShared_359_ = v_isSharedCheck_381_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_k_356_);
lean_dec(v_p_u2082_322_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_381_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_int_add(v_k_355_, v_k_356_);
lean_dec(v_k_356_);
lean_dec(v_k_355_);
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_360_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
lean_dec_ref(v___x_354_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_372_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_a_362_);
v___x_367_ = v___x_358_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_del_object(v___x_358_);
v_a_373_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_361_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_361_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v_k_382_; lean_object* v___x_383_; 
v_k_382_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_inc(v_k_382_);
lean_dec_ref(v_p_u2081_321_);
v___x_383_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2082_322_, v_k_382_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
lean_dec_ref(v___x_354_);
lean_dec(v_k_382_);
return v___x_383_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_322_) == 0)
{
lean_object* v_k_384_; lean_object* v___x_385_; 
v_k_384_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_inc(v_k_384_);
lean_dec_ref(v_p_u2082_322_);
v___x_385_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2081_321_, v_k_384_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
lean_dec_ref(v___x_354_);
lean_dec(v_k_384_);
return v___x_385_;
}
else
{
lean_object* v_k_386_; lean_object* v_v_387_; lean_object* v_p_388_; lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_p_391_; uint8_t v___x_392_; 
v_k_386_ = lean_ctor_get(v_p_u2081_321_, 0);
v_v_387_ = lean_ctor_get(v_p_u2081_321_, 1);
v_p_388_ = lean_ctor_get(v_p_u2081_321_, 2);
v_k_389_ = lean_ctor_get(v_p_u2082_322_, 0);
v_v_390_ = lean_ctor_get(v_p_u2082_322_, 1);
v_p_391_ = lean_ctor_get(v_p_u2082_322_, 2);
v___x_392_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_387_, v_v_390_);
switch(v___x_392_)
{
case 0:
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_408_; 
lean_inc_ref(v_p_391_);
lean_inc(v_v_390_);
lean_inc(v_k_389_);
v_isSharedCheck_408_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_409_ = lean_ctor_get(v_p_u2082_322_, 2);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_p_u2082_322_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_dec(v_unused_411_);
v___x_394_ = v_p_u2082_322_;
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_p_u2082_322_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_321_, v_p_391_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_407_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_407_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 2, v_a_397_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_k_389_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_v_390_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_a_397_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_del_object(v___x_394_);
lean_dec(v_v_390_);
lean_dec(v_k_389_);
return v___x_396_;
}
}
}
case 1:
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_441_; 
lean_inc_ref(v_p_391_);
lean_inc(v_k_389_);
lean_inc_ref(v_p_388_);
lean_inc(v_v_387_);
lean_inc(v_k_386_);
lean_dec_ref(v_p_u2081_321_);
v_isSharedCheck_441_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_442_ = lean_ctor_get(v_p_u2082_322_, 2);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_p_u2082_322_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_dec(v_unused_444_);
v___x_413_ = v_p_u2082_322_;
v_isShared_414_ = v_isSharedCheck_441_;
goto v_resetjp_412_;
}
else
{
lean_dec(v_p_u2082_322_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_441_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_int_add(v_k_386_, v_k_389_);
lean_dec(v_k_389_);
lean_dec(v_k_386_);
v___x_416_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_415_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref(v___x_416_);
v___x_418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_419_ = lean_int_dec_eq(v_a_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
v___x_420_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_388_, v_p_391_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 2, v_a_421_);
lean_ctor_set(v___x_413_, 1, v_v_387_);
lean_ctor_set(v___x_413_, 0, v_a_417_);
v___x_426_ = v___x_413_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_417_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_v_387_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_a_421_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_dec(v_a_417_);
lean_del_object(v___x_413_);
lean_dec(v_v_387_);
return v___x_420_;
}
}
else
{
lean_dec(v_a_417_);
lean_del_object(v___x_413_);
lean_dec(v_v_387_);
v_p_u2081_321_ = v_p_388_;
v_p_u2082_322_ = v_p_391_;
v_a_332_ = v___x_354_;
goto _start;
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_del_object(v___x_413_);
lean_dec_ref(v_p_391_);
lean_dec_ref(v_p_388_);
lean_dec(v_v_387_);
lean_dec_ref(v___x_354_);
v_a_433_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_416_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_416_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
default: 
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_460_; 
lean_inc_ref(v_p_388_);
lean_inc(v_v_387_);
lean_inc(v_k_386_);
v_isSharedCheck_460_ = !lean_is_exclusive(v_p_u2081_321_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_461_ = lean_ctor_get(v_p_u2081_321_, 2);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_p_u2081_321_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_dec(v_unused_463_);
v___x_446_ = v_p_u2081_321_;
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_p_u2081_321_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_388_, v_p_u2082_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_354_, v_a_333_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_459_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_459_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_459_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_459_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 2, v_a_449_);
v___x_454_ = v___x_446_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_k_386_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_v_387_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_a_449_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_del_object(v___x_446_);
lean_dec(v_v_387_);
lean_dec(v_k_386_);
return v___x_448_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object* v_p_u2081_468_, lean_object* v_p_u2082_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_468_, v_p_u2082_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object* v_p_u2081_483_, lean_object* v_p_u2082_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_, lean_object* v_h__3_487_, lean_object* v_h__4_488_){
_start:
{
if (lean_obj_tag(v_p_u2081_483_) == 0)
{
lean_dec(v_h__4_488_);
lean_dec(v_h__3_487_);
if (lean_obj_tag(v_p_u2082_484_) == 0)
{
lean_object* v_k_489_; lean_object* v_k_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_486_);
v_k_489_ = lean_ctor_get(v_p_u2081_483_, 0);
lean_inc(v_k_489_);
lean_dec_ref(v_p_u2081_483_);
v_k_490_ = lean_ctor_get(v_p_u2082_484_, 0);
lean_inc(v_k_490_);
lean_dec_ref(v_p_u2082_484_);
v___x_491_ = lean_apply_2(v_h__1_485_, v_k_489_, v_k_490_);
return v___x_491_;
}
else
{
lean_object* v_k_492_; lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_p_495_; lean_object* v___x_496_; 
lean_dec(v_h__1_485_);
v_k_492_ = lean_ctor_get(v_p_u2081_483_, 0);
lean_inc(v_k_492_);
lean_dec_ref(v_p_u2081_483_);
v_k_493_ = lean_ctor_get(v_p_u2082_484_, 0);
lean_inc(v_k_493_);
v_v_494_ = lean_ctor_get(v_p_u2082_484_, 1);
lean_inc(v_v_494_);
v_p_495_ = lean_ctor_get(v_p_u2082_484_, 2);
lean_inc_ref(v_p_495_);
lean_dec_ref(v_p_u2082_484_);
v___x_496_ = lean_apply_4(v_h__2_486_, v_k_492_, v_k_493_, v_v_494_, v_p_495_);
return v___x_496_;
}
}
else
{
lean_dec(v_h__2_486_);
lean_dec(v_h__1_485_);
if (lean_obj_tag(v_p_u2082_484_) == 0)
{
lean_object* v_k_497_; lean_object* v_v_498_; lean_object* v_p_499_; lean_object* v_k_500_; lean_object* v___x_501_; 
lean_dec(v_h__4_488_);
v_k_497_ = lean_ctor_get(v_p_u2081_483_, 0);
lean_inc(v_k_497_);
v_v_498_ = lean_ctor_get(v_p_u2081_483_, 1);
lean_inc(v_v_498_);
v_p_499_ = lean_ctor_get(v_p_u2081_483_, 2);
lean_inc_ref(v_p_499_);
lean_dec_ref(v_p_u2081_483_);
v_k_500_ = lean_ctor_get(v_p_u2082_484_, 0);
lean_inc(v_k_500_);
lean_dec_ref(v_p_u2082_484_);
v___x_501_ = lean_apply_4(v_h__3_487_, v_k_497_, v_v_498_, v_p_499_, v_k_500_);
return v___x_501_;
}
else
{
lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v_p_504_; lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v_p_507_; lean_object* v___x_508_; 
lean_dec(v_h__3_487_);
v_k_502_ = lean_ctor_get(v_p_u2081_483_, 0);
lean_inc(v_k_502_);
v_v_503_ = lean_ctor_get(v_p_u2081_483_, 1);
lean_inc(v_v_503_);
v_p_504_ = lean_ctor_get(v_p_u2081_483_, 2);
lean_inc_ref(v_p_504_);
lean_dec_ref(v_p_u2081_483_);
v_k_505_ = lean_ctor_get(v_p_u2082_484_, 0);
lean_inc(v_k_505_);
v_v_506_ = lean_ctor_get(v_p_u2082_484_, 1);
lean_inc(v_v_506_);
v_p_507_ = lean_ctor_get(v_p_u2082_484_, 2);
lean_inc_ref(v_p_507_);
lean_dec_ref(v_p_u2082_484_);
v___x_508_ = lean_apply_6(v_h__4_488_, v_k_502_, v_v_503_, v_p_504_, v_k_505_, v_v_506_, v_p_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object* v_motive_509_, lean_object* v_p_u2081_510_, lean_object* v_p_u2082_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_, lean_object* v_h__3_514_, lean_object* v_h__4_515_){
_start:
{
if (lean_obj_tag(v_p_u2081_510_) == 0)
{
lean_dec(v_h__4_515_);
lean_dec(v_h__3_514_);
if (lean_obj_tag(v_p_u2082_511_) == 0)
{
lean_object* v_k_516_; lean_object* v_k_517_; lean_object* v___x_518_; 
lean_dec(v_h__2_513_);
v_k_516_ = lean_ctor_get(v_p_u2081_510_, 0);
lean_inc(v_k_516_);
lean_dec_ref(v_p_u2081_510_);
v_k_517_ = lean_ctor_get(v_p_u2082_511_, 0);
lean_inc(v_k_517_);
lean_dec_ref(v_p_u2082_511_);
v___x_518_ = lean_apply_2(v_h__1_512_, v_k_516_, v_k_517_);
return v___x_518_;
}
else
{
lean_object* v_k_519_; lean_object* v_k_520_; lean_object* v_v_521_; lean_object* v_p_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_512_);
v_k_519_ = lean_ctor_get(v_p_u2081_510_, 0);
lean_inc(v_k_519_);
lean_dec_ref(v_p_u2081_510_);
v_k_520_ = lean_ctor_get(v_p_u2082_511_, 0);
lean_inc(v_k_520_);
v_v_521_ = lean_ctor_get(v_p_u2082_511_, 1);
lean_inc(v_v_521_);
v_p_522_ = lean_ctor_get(v_p_u2082_511_, 2);
lean_inc_ref(v_p_522_);
lean_dec_ref(v_p_u2082_511_);
v___x_523_ = lean_apply_4(v_h__2_513_, v_k_519_, v_k_520_, v_v_521_, v_p_522_);
return v___x_523_;
}
}
else
{
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
if (lean_obj_tag(v_p_u2082_511_) == 0)
{
lean_object* v_k_524_; lean_object* v_v_525_; lean_object* v_p_526_; lean_object* v_k_527_; lean_object* v___x_528_; 
lean_dec(v_h__4_515_);
v_k_524_ = lean_ctor_get(v_p_u2081_510_, 0);
lean_inc(v_k_524_);
v_v_525_ = lean_ctor_get(v_p_u2081_510_, 1);
lean_inc(v_v_525_);
v_p_526_ = lean_ctor_get(v_p_u2081_510_, 2);
lean_inc_ref(v_p_526_);
lean_dec_ref(v_p_u2081_510_);
v_k_527_ = lean_ctor_get(v_p_u2082_511_, 0);
lean_inc(v_k_527_);
lean_dec_ref(v_p_u2082_511_);
v___x_528_ = lean_apply_4(v_h__3_514_, v_k_524_, v_v_525_, v_p_526_, v_k_527_);
return v___x_528_;
}
else
{
lean_object* v_k_529_; lean_object* v_v_530_; lean_object* v_p_531_; lean_object* v_k_532_; lean_object* v_v_533_; lean_object* v_p_534_; lean_object* v___x_535_; 
lean_dec(v_h__3_514_);
v_k_529_ = lean_ctor_get(v_p_u2081_510_, 0);
lean_inc(v_k_529_);
v_v_530_ = lean_ctor_get(v_p_u2081_510_, 1);
lean_inc(v_v_530_);
v_p_531_ = lean_ctor_get(v_p_u2081_510_, 2);
lean_inc_ref(v_p_531_);
lean_dec_ref(v_p_u2081_510_);
v_k_532_ = lean_ctor_get(v_p_u2082_511_, 0);
lean_inc(v_k_532_);
v_v_533_ = lean_ctor_get(v_p_u2082_511_, 1);
lean_inc(v_v_533_);
v_p_534_ = lean_ctor_get(v_p_u2082_511_, 2);
lean_inc_ref(v_p_534_);
lean_dec_ref(v_p_u2082_511_);
v___x_535_ = lean_apply_6(v_h__4_515_, v_k_529_, v_v_530_, v_p_531_, v_k_532_, v_v_533_, v_p_534_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t v_x_536_, lean_object* v_h__1_537_, lean_object* v_h__2_538_, lean_object* v_h__3_539_){
_start:
{
switch(v_x_536_)
{
case 0:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v_h__2_538_);
lean_dec(v_h__1_537_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_apply_1(v_h__3_539_, v___x_540_);
return v___x_541_;
}
case 1:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_h__3_539_);
lean_dec(v_h__2_538_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_apply_1(v_h__1_537_, v___x_542_);
return v___x_543_;
}
default: 
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__3_539_);
lean_dec(v_h__1_537_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__2_538_, v___x_544_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object* v_x_546_, lean_object* v_h__1_547_, lean_object* v_h__2_548_, lean_object* v_h__3_549_){
_start:
{
uint8_t v_x_36__boxed_550_; lean_object* v_res_551_; 
v_x_36__boxed_550_ = lean_unbox(v_x_546_);
v_res_551_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_36__boxed_550_, v_h__1_547_, v_h__2_548_, v_h__3_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object* v_motive_552_, uint8_t v_x_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_, lean_object* v_h__3_556_){
_start:
{
switch(v_x_553_)
{
case 0:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_h__2_555_);
lean_dec(v_h__1_554_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v_h__3_556_, v___x_557_);
return v___x_558_;
}
case 1:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_h__3_556_);
lean_dec(v_h__2_555_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_1(v_h__1_554_, v___x_559_);
return v___x_560_;
}
default: 
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_h__3_556_);
lean_dec(v_h__1_554_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_apply_1(v_h__2_555_, v___x_561_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object* v_motive_563_, lean_object* v_x_564_, lean_object* v_h__1_565_, lean_object* v_h__2_566_, lean_object* v_h__3_567_){
_start:
{
uint8_t v_x_51__boxed_568_; lean_object* v_res_569_; 
v_x_51__boxed_568_ = lean_unbox(v_x_564_);
v_res_569_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_563_, v_x_51__boxed_568_, v_h__1_565_, v_h__2_566_, v_h__3_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object* v_p_u2082_571_, lean_object* v_p_u2081_572_, lean_object* v_acc_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_fileName_586_; lean_object* v_fileMap_587_; lean_object* v_options_588_; lean_object* v_currRecDepth_589_; lean_object* v_maxRecDepth_590_; lean_object* v_ref_591_; lean_object* v_currNamespace_592_; lean_object* v_openDecls_593_; lean_object* v_initHeartbeats_594_; lean_object* v_maxHeartbeats_595_; lean_object* v_quotContext_596_; lean_object* v_currMacroScope_597_; uint8_t v_diag_598_; lean_object* v_cancelTk_x3f_599_; uint8_t v_suppressElabErrors_600_; lean_object* v_inheritedTraceOptions_601_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_fileName_586_ = lean_ctor_get(v_a_583_, 0);
lean_inc_ref(v_fileName_586_);
v_fileMap_587_ = lean_ctor_get(v_a_583_, 1);
lean_inc_ref(v_fileMap_587_);
v_options_588_ = lean_ctor_get(v_a_583_, 2);
lean_inc_ref(v_options_588_);
v_currRecDepth_589_ = lean_ctor_get(v_a_583_, 3);
lean_inc(v_currRecDepth_589_);
v_maxRecDepth_590_ = lean_ctor_get(v_a_583_, 4);
lean_inc(v_maxRecDepth_590_);
v_ref_591_ = lean_ctor_get(v_a_583_, 5);
lean_inc(v_ref_591_);
v_currNamespace_592_ = lean_ctor_get(v_a_583_, 6);
lean_inc(v_currNamespace_592_);
v_openDecls_593_ = lean_ctor_get(v_a_583_, 7);
lean_inc(v_openDecls_593_);
v_initHeartbeats_594_ = lean_ctor_get(v_a_583_, 8);
lean_inc(v_initHeartbeats_594_);
v_maxHeartbeats_595_ = lean_ctor_get(v_a_583_, 9);
lean_inc(v_maxHeartbeats_595_);
v_quotContext_596_ = lean_ctor_get(v_a_583_, 10);
lean_inc(v_quotContext_596_);
v_currMacroScope_597_ = lean_ctor_get(v_a_583_, 11);
lean_inc(v_currMacroScope_597_);
v_diag_598_ = lean_ctor_get_uint8(v_a_583_, sizeof(void*)*14);
v_cancelTk_x3f_599_ = lean_ctor_get(v_a_583_, 12);
lean_inc(v_cancelTk_x3f_599_);
v_suppressElabErrors_600_ = lean_ctor_get_uint8(v_a_583_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_601_ = lean_ctor_get(v_a_583_, 13);
lean_inc_ref(v_inheritedTraceOptions_601_);
lean_dec_ref(v_a_583_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v_maxRecDepth_590_, v___x_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
v___x_630_ = lean_nat_dec_eq(v_currRecDepth_589_, v_maxRecDepth_590_);
if (v___x_630_ == 0)
{
goto v___jp_602_;
}
else
{
lean_object* v___x_631_; 
lean_dec_ref(v_inheritedTraceOptions_601_);
lean_dec(v_cancelTk_x3f_599_);
lean_dec(v_currMacroScope_597_);
lean_dec(v_quotContext_596_);
lean_dec(v_maxHeartbeats_595_);
lean_dec(v_initHeartbeats_594_);
lean_dec(v_openDecls_593_);
lean_dec(v_currNamespace_592_);
lean_dec(v_maxRecDepth_590_);
lean_dec(v_currRecDepth_589_);
lean_dec_ref(v_options_588_);
lean_dec_ref(v_fileMap_587_);
lean_dec_ref(v_fileName_586_);
lean_dec_ref(v_acc_573_);
lean_dec_ref(v_p_u2081_572_);
lean_dec_ref(v_p_u2082_571_);
v___x_631_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_591_);
return v___x_631_;
}
}
else
{
goto v___jp_602_;
}
v___jp_602_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_currRecDepth_589_, v___x_603_);
lean_dec(v_currRecDepth_589_);
v___x_605_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_605_, 0, v_fileName_586_);
lean_ctor_set(v___x_605_, 1, v_fileMap_587_);
lean_ctor_set(v___x_605_, 2, v_options_588_);
lean_ctor_set(v___x_605_, 3, v___x_604_);
lean_ctor_set(v___x_605_, 4, v_maxRecDepth_590_);
lean_ctor_set(v___x_605_, 5, v_ref_591_);
lean_ctor_set(v___x_605_, 6, v_currNamespace_592_);
lean_ctor_set(v___x_605_, 7, v_openDecls_593_);
lean_ctor_set(v___x_605_, 8, v_initHeartbeats_594_);
lean_ctor_set(v___x_605_, 9, v_maxHeartbeats_595_);
lean_ctor_set(v___x_605_, 10, v_quotContext_596_);
lean_ctor_set(v___x_605_, 11, v_currMacroScope_597_);
lean_ctor_set(v___x_605_, 12, v_cancelTk_x3f_599_);
lean_ctor_set(v___x_605_, 13, v_inheritedTraceOptions_601_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*14, v_diag_598_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*14 + 1, v_suppressElabErrors_600_);
if (lean_obj_tag(v_p_u2081_572_) == 0)
{
lean_object* v_k_606_; lean_object* v___x_607_; 
v_k_606_ = lean_ctor_get(v_p_u2081_572_, 0);
lean_inc(v_k_606_);
lean_dec_ref(v_p_u2081_572_);
v___x_607_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_606_, v_p_u2082_571_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v___x_605_, v_a_584_);
lean_dec(v_k_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_573_, v_a_608_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v___x_605_, v_a_584_);
return v___x_609_;
}
else
{
lean_dec_ref(v___x_605_);
lean_dec_ref(v_acc_573_);
return v___x_607_;
}
}
else
{
lean_object* v_k_610_; lean_object* v_v_611_; lean_object* v_p_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_k_610_ = lean_ctor_get(v_p_u2081_572_, 0);
lean_inc(v_k_610_);
v_v_611_ = lean_ctor_get(v_p_u2081_572_, 1);
lean_inc(v_v_611_);
v_p_612_ = lean_ctor_get(v_p_u2081_572_, 2);
lean_inc_ref(v_p_612_);
lean_dec_ref(v_p_u2081_572_);
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
v___x_614_ = l_Lean_Core_checkSystem(v___x_613_, v___x_605_, v_a_584_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_615_; 
lean_dec_ref(v___x_614_);
lean_inc_ref(v_p_u2082_571_);
v___x_615_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_610_, v_v_611_, v_p_u2082_571_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v___x_605_, v_a_584_);
lean_dec(v_k_610_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref(v___x_615_);
lean_inc_ref(v___x_605_);
v___x_617_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_573_, v_a_616_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v___x_605_, v_a_584_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v___x_617_);
v_p_u2081_572_ = v_p_612_;
v_acc_573_ = v_a_618_;
v_a_583_ = v___x_605_;
goto _start;
}
else
{
lean_dec_ref(v_p_612_);
lean_dec_ref(v___x_605_);
lean_dec_ref(v_p_u2082_571_);
return v___x_617_;
}
}
else
{
lean_dec_ref(v_p_612_);
lean_dec_ref(v___x_605_);
lean_dec_ref(v_acc_573_);
lean_dec_ref(v_p_u2082_571_);
return v___x_615_;
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_p_612_);
lean_dec(v_v_611_);
lean_dec(v_k_610_);
lean_dec_ref(v___x_605_);
lean_dec_ref(v_acc_573_);
lean_dec_ref(v_p_u2082_571_);
v_a_620_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_614_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_614_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object* v_p_u2082_632_, lean_object* v_p_u2081_633_, lean_object* v_acc_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_632_, v_p_u2081_633_, v_acc_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object* v_p_u2081_650_, lean_object* v_p_u2082_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
lean_inc_ref(v_a_661_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_651_, v_p_u2081_650_, v___x_664_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object* v_p_u2081_666_, lean_object* v_p_u2082_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_666_, v_p_u2082_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
return v_res_680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_to_int(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object* v_p_685_, lean_object* v_k_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_fileName_699_; lean_object* v_fileMap_700_; lean_object* v_options_701_; lean_object* v_currRecDepth_702_; lean_object* v_maxRecDepth_703_; lean_object* v_ref_704_; lean_object* v_currNamespace_705_; lean_object* v_openDecls_706_; lean_object* v_initHeartbeats_707_; lean_object* v_maxHeartbeats_708_; lean_object* v_quotContext_709_; lean_object* v_currMacroScope_710_; uint8_t v_diag_711_; lean_object* v_cancelTk_x3f_712_; uint8_t v_suppressElabErrors_713_; lean_object* v_inheritedTraceOptions_714_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_fileName_699_ = lean_ctor_get(v_a_696_, 0);
v_fileMap_700_ = lean_ctor_get(v_a_696_, 1);
v_options_701_ = lean_ctor_get(v_a_696_, 2);
v_currRecDepth_702_ = lean_ctor_get(v_a_696_, 3);
v_maxRecDepth_703_ = lean_ctor_get(v_a_696_, 4);
v_ref_704_ = lean_ctor_get(v_a_696_, 5);
v_currNamespace_705_ = lean_ctor_get(v_a_696_, 6);
v_openDecls_706_ = lean_ctor_get(v_a_696_, 7);
v_initHeartbeats_707_ = lean_ctor_get(v_a_696_, 8);
v_maxHeartbeats_708_ = lean_ctor_get(v_a_696_, 9);
v_quotContext_709_ = lean_ctor_get(v_a_696_, 10);
v_currMacroScope_710_ = lean_ctor_get(v_a_696_, 11);
v_diag_711_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*14);
v_cancelTk_x3f_712_ = lean_ctor_get(v_a_696_, 12);
v_suppressElabErrors_713_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_714_ = lean_ctor_get(v_a_696_, 13);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_nat_dec_eq(v_maxRecDepth_703_, v___x_735_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_eq(v_currRecDepth_702_, v_maxRecDepth_703_);
if (v___x_737_ == 0)
{
goto v___jp_715_;
}
else
{
lean_object* v___x_738_; 
lean_dec_ref(v_p_685_);
lean_inc(v_ref_704_);
v___x_738_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_704_);
return v___x_738_;
}
}
else
{
goto v___jp_715_;
}
v___jp_715_:
{
lean_object* v_zero_716_; uint8_t v_isZero_717_; 
v_zero_716_ = lean_unsigned_to_nat(0u);
v_isZero_717_ = lean_nat_dec_eq(v_k_686_, v_zero_716_);
if (v_isZero_717_ == 1)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_p_685_);
v___x_718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v_one_720_; lean_object* v_n_721_; uint8_t v_isZero_722_; 
v_one_720_ = lean_unsigned_to_nat(1u);
v_n_721_ = lean_nat_sub(v_k_686_, v_one_720_);
v_isZero_722_ = lean_nat_dec_eq(v_n_721_, v_zero_716_);
if (v_isZero_722_ == 1)
{
lean_object* v___x_723_; 
lean_dec(v_n_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_p_685_);
return v___x_723_;
}
else
{
lean_object* v_n_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v_isZero_727_; 
v_n_724_ = lean_nat_sub(v_n_721_, v_one_720_);
lean_dec(v_n_721_);
v___x_725_ = lean_nat_add(v_currRecDepth_702_, v_one_720_);
lean_inc_ref(v_inheritedTraceOptions_714_);
lean_inc(v_cancelTk_x3f_712_);
lean_inc(v_currMacroScope_710_);
lean_inc(v_quotContext_709_);
lean_inc(v_maxHeartbeats_708_);
lean_inc(v_initHeartbeats_707_);
lean_inc(v_openDecls_706_);
lean_inc(v_currNamespace_705_);
lean_inc(v_ref_704_);
lean_inc(v_maxRecDepth_703_);
lean_inc_ref(v_options_701_);
lean_inc_ref(v_fileMap_700_);
lean_inc_ref(v_fileName_699_);
v___x_726_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_726_, 0, v_fileName_699_);
lean_ctor_set(v___x_726_, 1, v_fileMap_700_);
lean_ctor_set(v___x_726_, 2, v_options_701_);
lean_ctor_set(v___x_726_, 3, v___x_725_);
lean_ctor_set(v___x_726_, 4, v_maxRecDepth_703_);
lean_ctor_set(v___x_726_, 5, v_ref_704_);
lean_ctor_set(v___x_726_, 6, v_currNamespace_705_);
lean_ctor_set(v___x_726_, 7, v_openDecls_706_);
lean_ctor_set(v___x_726_, 8, v_initHeartbeats_707_);
lean_ctor_set(v___x_726_, 9, v_maxHeartbeats_708_);
lean_ctor_set(v___x_726_, 10, v_quotContext_709_);
lean_ctor_set(v___x_726_, 11, v_currMacroScope_710_);
lean_ctor_set(v___x_726_, 12, v_cancelTk_x3f_712_);
lean_ctor_set(v___x_726_, 13, v_inheritedTraceOptions_714_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*14, v_diag_711_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*14 + 1, v_suppressElabErrors_713_);
v_isZero_727_ = lean_nat_dec_eq(v_n_724_, v_zero_716_);
if (v_isZero_727_ == 1)
{
lean_object* v___x_728_; 
lean_dec(v_n_724_);
lean_inc_ref(v_p_685_);
v___x_728_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_685_, v_p_685_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v___x_726_, v_a_697_);
lean_dec_ref(v___x_726_);
return v___x_728_;
}
else
{
lean_object* v_n_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_n_729_ = lean_nat_sub(v_n_724_, v_one_720_);
lean_dec(v_n_724_);
v___x_730_ = lean_unsigned_to_nat(2u);
v___x_731_ = lean_nat_add(v_n_729_, v___x_730_);
lean_dec(v_n_729_);
lean_inc_ref(v_p_685_);
v___x_732_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_685_, v___x_731_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v___x_726_, v_a_697_);
lean_dec(v___x_731_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref(v___x_732_);
v___x_734_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_685_, v_a_733_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v___x_726_, v_a_697_);
lean_dec_ref(v___x_726_);
return v___x_734_;
}
else
{
lean_dec_ref(v___x_726_);
lean_dec_ref(v_p_685_);
return v___x_732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object* v_p_739_, lean_object* v_k_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_739_, v_k_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_k_740_);
return v_res_753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_755_ = lean_int_neg(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object* v_e_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_n_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; 
switch(lean_obj_tag(v_e_758_))
{
case 1:
{
lean_object* v_k_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_829_; 
v_k_803_ = lean_ctor_get(v_e_758_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_e_758_);
if (v_isSharedCheck_829_ == 0)
{
v___x_805_ = v_e_758_;
v_isShared_806_ = v_isSharedCheck_829_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_k_803_);
lean_dec(v_e_758_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_829_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_nat_to_int(v_k_803_);
v___x_808_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_807_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_820_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_820_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 0);
lean_ctor_set(v___x_805_, 0, v_a_809_);
v___x_814_ = v___x_805_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_819_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
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
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_del_object(v___x_805_);
v_a_821_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_808_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_808_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
case 3:
{
lean_object* v_i_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_839_; 
v_i_830_ = lean_ctor_get(v_e_758_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_e_758_);
if (v_isSharedCheck_839_ == 0)
{
v___x_832_ = v_e_758_;
v_isShared_833_ = v_isSharedCheck_839_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_i_830_);
lean_dec(v_e_758_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_839_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 1);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
}
case 4:
{
lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_840_ = lean_ctor_get(v_e_758_, 0);
lean_inc_ref(v_a_840_);
lean_dec_ref(v_e_758_);
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_840_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
if (lean_obj_tag(v_a_842_) == 0)
{
return v___x_841_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v___x_841_);
v_val_843_ = lean_ctor_get(v_a_842_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v_a_842_);
if (v_isSharedCheck_868_ == 0)
{
v___x_845_ = v_a_842_;
v_isShared_846_ = v_isSharedCheck_868_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_val_843_);
lean_dec(v_a_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_868_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_847_, v_val_843_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_859_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_a_849_);
v___x_854_ = v___x_845_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_del_object(v___x_845_);
v_a_860_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_848_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_848_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
return v___x_841_;
}
}
case 5:
{
lean_object* v_a_869_; lean_object* v_b_870_; lean_object* v___x_871_; 
v_a_869_ = lean_ctor_get(v_e_758_, 0);
lean_inc_ref(v_a_869_);
v_b_870_ = lean_ctor_get(v_e_758_, 1);
lean_inc_ref(v_b_870_);
lean_dec_ref(v_e_758_);
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_869_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
if (lean_obj_tag(v_a_872_) == 0)
{
lean_dec_ref(v_b_870_);
return v___x_871_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; 
lean_dec_ref(v___x_871_);
v_val_873_ = lean_ctor_get(v_a_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v_a_872_);
v___x_874_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_870_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
if (lean_obj_tag(v_a_875_) == 0)
{
lean_dec(v_val_873_);
return v___x_874_;
}
else
{
lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___x_874_);
v_val_876_ = lean_ctor_get(v_a_875_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_900_ == 0)
{
v___x_878_ = v_a_875_;
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_dec(v_a_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; 
lean_inc_ref(v_a_768_);
v___x_880_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_873_, v_val_876_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_891_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_891_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_891_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_891_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_a_881_);
v___x_886_ = v___x_878_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_del_object(v___x_878_);
v_a_892_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_880_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_880_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
else
{
lean_dec(v_val_873_);
return v___x_874_;
}
}
}
else
{
lean_dec_ref(v_b_870_);
return v___x_871_;
}
}
case 6:
{
lean_object* v_a_901_; lean_object* v_b_902_; lean_object* v___x_903_; 
v_a_901_ = lean_ctor_get(v_e_758_, 0);
lean_inc_ref(v_a_901_);
v_b_902_ = lean_ctor_get(v_e_758_, 1);
lean_inc_ref(v_b_902_);
lean_dec_ref(v_e_758_);
v___x_903_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_901_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
if (lean_obj_tag(v_a_904_) == 0)
{
lean_dec_ref(v_b_902_);
return v___x_903_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_906_; 
lean_dec_ref(v___x_903_);
v_val_905_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref(v_a_904_);
v___x_906_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_902_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
if (lean_obj_tag(v_a_907_) == 0)
{
lean_dec(v_val_905_);
return v___x_906_;
}
else
{
lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v___x_906_);
v_val_908_ = lean_ctor_get(v_a_907_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_943_ == 0)
{
v___x_910_ = v_a_907_;
v_isShared_911_ = v_isSharedCheck_943_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_dec(v_a_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_943_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_913_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_912_, v_val_908_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
lean_inc_ref(v_a_768_);
v___x_915_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_905_, v_a_914_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_926_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_a_916_);
v___x_921_ = v___x_910_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_del_object(v___x_910_);
v_a_927_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_915_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_915_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_del_object(v___x_910_);
lean_dec(v_val_905_);
v_a_935_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_913_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_913_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
else
{
lean_dec(v_val_905_);
return v___x_906_;
}
}
}
else
{
lean_dec_ref(v_b_902_);
return v___x_903_;
}
}
case 7:
{
lean_object* v_a_944_; lean_object* v_b_945_; lean_object* v___x_946_; 
v_a_944_ = lean_ctor_get(v_e_758_, 0);
lean_inc_ref(v_a_944_);
v_b_945_ = lean_ctor_get(v_e_758_, 1);
lean_inc_ref(v_b_945_);
lean_dec_ref(v_e_758_);
v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_944_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
if (lean_obj_tag(v_a_947_) == 0)
{
lean_dec_ref(v_b_945_);
return v___x_946_;
}
else
{
lean_object* v_val_948_; lean_object* v___x_949_; 
lean_dec_ref(v___x_946_);
v_val_948_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref(v_a_947_);
v___x_949_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_945_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
if (lean_obj_tag(v_a_950_) == 0)
{
lean_dec(v_val_948_);
return v___x_949_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v___x_949_);
v_val_951_ = lean_ctor_get(v_a_950_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_975_ == 0)
{
v___x_953_ = v_a_950_;
v_isShared_954_ = v_isSharedCheck_975_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v_a_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_975_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_val_948_, v_val_951_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_966_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_966_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_966_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_966_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_a_956_);
v___x_961_ = v___x_953_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
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
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_953_);
v_a_967_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_955_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_955_);
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
}
}
else
{
lean_dec(v_val_948_);
return v___x_949_;
}
}
}
else
{
lean_dec_ref(v_b_945_);
return v___x_946_;
}
}
case 8:
{
lean_object* v_a_976_; lean_object* v_k_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1073_; 
v_a_976_ = lean_ctor_get(v_e_758_, 0);
v_k_977_ = lean_ctor_get(v_e_758_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_e_758_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_979_ = v_e_758_;
v_isShared_980_ = v_isSharedCheck_1073_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_k_977_);
lean_inc(v_a_976_);
lean_dec(v_e_758_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1073_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_nat_dec_eq(v_k_977_, v___x_981_);
if (v___x_982_ == 0)
{
switch(lean_obj_tag(v_a_976_))
{
case 0:
{
lean_object* v_k_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_979_);
v_k_983_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_985_ = v_a_976_;
v_isShared_986_ = v_isSharedCheck_1028_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_k_983_);
lean_dec(v_a_976_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1028_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; 
lean_inc(v_k_977_);
v___x_987_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_k_977_, v_a_762_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1019_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1019_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1019_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
if (lean_obj_tag(v_a_988_) == 0)
{
if (v___x_982_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_del_object(v___x_985_);
lean_dec(v_k_983_);
lean_dec(v_k_977_);
v___x_1015_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_1015_);
v___x_1017_ = v___x_990_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_del_object(v___x_990_);
goto v___jp_992_;
}
}
else
{
lean_dec_ref(v_a_988_);
lean_del_object(v___x_990_);
goto v___jp_992_;
}
v___jp_992_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l_Int_pow(v_k_983_, v_k_977_);
lean_dec(v_k_977_);
lean_dec(v_k_983_);
v___x_994_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_993_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1006_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v_a_995_);
v___x_1000_ = v___x_985_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1005_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1001_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
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
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_del_object(v___x_985_);
v_a_1007_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_994_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_994_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_985_);
lean_dec(v_k_983_);
lean_dec(v_k_977_);
v_a_1020_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_987_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_987_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
v_i_1029_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1031_ = v_a_976_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_i_1029_);
lean_dec(v_a_976_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 0);
lean_ctor_set(v___x_979_, 0, v_i_1029_);
v___x_1034_ = v___x_979_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_i_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_k_977_);
v___x_1034_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_1036_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1037_);
v___x_1039_ = v___x_1031_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
}
}
default: 
{
lean_object* v___x_1044_; 
lean_del_object(v___x_979_);
v___x_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_976_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
if (lean_obj_tag(v_a_1045_) == 0)
{
lean_dec(v_k_977_);
return v___x_1044_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v___x_1044_);
v_val_1046_ = lean_ctor_get(v_a_1045_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_a_1045_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1048_ = v_a_1045_;
v_isShared_1049_ = v_isSharedCheck_1070_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_val_1046_);
lean_dec(v_a_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1070_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_1046_, v_k_977_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_k_977_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_a_1051_);
v___x_1056_ = v___x_1048_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1056_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_del_object(v___x_1048_);
v_a_1062_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1050_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1050_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
else
{
lean_dec(v_k_977_);
return v___x_1044_;
}
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_del_object(v___x_979_);
lean_dec(v_k_977_);
lean_dec_ref(v_a_976_);
v___x_1071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
}
default: 
{
lean_object* v_k_1074_; 
v_k_1074_ = lean_ctor_get(v_e_758_, 0);
lean_inc(v_k_1074_);
lean_dec_ref(v_e_758_);
v_n_772_ = v_k_1074_;
v___y_773_ = v_a_759_;
v___y_774_ = v_a_760_;
v___y_775_ = v_a_761_;
v___y_776_ = v_a_762_;
v___y_777_ = v_a_763_;
v___y_778_ = v_a_764_;
v___y_779_ = v_a_765_;
v___y_780_ = v_a_766_;
v___y_781_ = v_a_767_;
v___y_782_ = v_a_768_;
v___y_783_ = v_a_769_;
goto v___jp_771_;
}
}
v___jp_771_:
{
lean_object* v___x_784_; 
v___x_784_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_n_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_794_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_794_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_a_785_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_a_795_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_784_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_784_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object* v_e_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_1117_, lean_object* v_k_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1118_, v_p_1117_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_1132_, lean_object* v_k_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1132_, v_k_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_k_1133_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_1147_, lean_object* v_k_1148_, lean_object* v_m_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1148_, v_m_1149_, v_p_1147_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_1163_, lean_object* v_k_1164_, lean_object* v_m_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1163_, v_k_1164_, v_m_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_k_1164_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_1179_, lean_object* v_p_u2082_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_1179_, v_p_u2082_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_1194_, lean_object* v_p_u2082_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_1194_, v_p_u2082_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_1209_, lean_object* v_p_u2082_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1223_; 
lean_inc_ref(v_a_1220_);
v___x_1223_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_1209_, v_p_u2082_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1224_, lean_object* v_p_u2082_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1224_, v_p_u2082_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1238_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
v___x_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1240_);
lean_ctor_set(v___x_1242_, 2, v___x_1239_);
lean_ctor_set(v___x_1242_, 3, v___x_1240_);
lean_ctor_set(v___x_1242_, 4, v___x_1239_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1243_, lean_object* v_p_u2082_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
if (lean_obj_tag(v_p_u2081_1243_) == 1)
{
if (lean_obj_tag(v_p_u2082_1244_) == 1)
{
lean_object* v_k_1260_; lean_object* v_v_1261_; lean_object* v_p_1262_; lean_object* v_k_1263_; lean_object* v_v_1264_; lean_object* v_p_1265_; lean_object* v_m_1266_; lean_object* v_m_u2081_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_g_1270_; lean_object* v___x_1271_; lean_object* v_c_u2081_1272_; lean_object* v___x_1273_; 
v_k_1260_ = lean_ctor_get(v_p_u2081_1243_, 0);
lean_inc(v_k_1260_);
v_v_1261_ = lean_ctor_get(v_p_u2081_1243_, 1);
lean_inc_n(v_v_1261_, 2);
v_p_1262_ = lean_ctor_get(v_p_u2081_1243_, 2);
lean_inc_ref(v_p_1262_);
lean_dec_ref(v_p_u2081_1243_);
v_k_1263_ = lean_ctor_get(v_p_u2082_1244_, 0);
lean_inc(v_k_1263_);
v_v_1264_ = lean_ctor_get(v_p_u2082_1244_, 1);
lean_inc_n(v_v_1264_, 2);
v_p_1265_ = lean_ctor_get(v_p_u2082_1244_, 2);
lean_inc_ref(v_p_1265_);
lean_dec_ref(v_p_u2082_1244_);
v_m_1266_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1261_, v_v_1264_);
lean_inc(v_m_1266_);
v_m_u2081_1267_ = l_Lean_Grind_CommRing_Mon_div(v_m_1266_, v_v_1261_);
v___x_1268_ = lean_nat_abs(v_k_1260_);
v___x_1269_ = lean_nat_abs(v_k_1263_);
v_g_1270_ = lean_nat_gcd(v___x_1268_, v___x_1269_);
lean_dec(v___x_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_nat_to_int(v_g_1270_);
v_c_u2081_1272_ = lean_int_ediv(v_k_1263_, v___x_1271_);
lean_dec(v_k_1263_);
lean_inc(v_m_u2081_1267_);
v___x_1273_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_1272_, v_m_u2081_1267_, v_p_1262_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_m_u2082_1275_; lean_object* v___x_1276_; lean_object* v_c_u2082_1277_; lean_object* v___x_1278_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1273_);
v_m_u2082_1275_ = l_Lean_Grind_CommRing_Mon_div(v_m_1266_, v_v_1264_);
v___x_1276_ = lean_int_neg(v_k_1260_);
lean_dec(v_k_1260_);
v_c_u2082_1277_ = lean_int_ediv(v___x_1276_, v___x_1271_);
lean_dec(v___x_1271_);
lean_dec(v___x_1276_);
lean_inc(v_m_u2082_1275_);
v___x_1278_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_1277_, v_m_u2082_1275_, v_p_1265_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
lean_inc_ref(v_a_1254_);
v___x_1280_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1274_, v_a_1279_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1285_, 0, v_a_1281_);
lean_ctor_set(v___x_1285_, 1, v_c_u2081_1272_);
lean_ctor_set(v___x_1285_, 2, v_m_u2081_1267_);
lean_ctor_set(v___x_1285_, 3, v_c_u2082_1277_);
lean_ctor_set(v___x_1285_, 4, v_m_u2082_1275_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_c_u2082_1277_);
lean_dec(v_m_u2082_1275_);
lean_dec(v_c_u2081_1272_);
lean_dec(v_m_u2081_1267_);
v_a_1290_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1280_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1280_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_c_u2082_1277_);
lean_dec(v_m_u2082_1275_);
lean_dec(v_a_1274_);
lean_dec(v_c_u2081_1272_);
lean_dec(v_m_u2081_1267_);
v_a_1298_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1278_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1278_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_c_u2081_1272_);
lean_dec(v___x_1271_);
lean_dec(v_m_u2081_1267_);
lean_dec(v_m_1266_);
lean_dec_ref(v_p_1265_);
lean_dec(v_v_1264_);
lean_dec(v_k_1260_);
v_a_1306_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1273_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1273_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_dec_ref(v_p_u2081_1243_);
lean_dec_ref(v_p_u2082_1244_);
goto v___jp_1257_;
}
}
else
{
lean_dec_ref(v_p_u2082_1244_);
lean_dec_ref(v_p_u2081_1243_);
goto v___jp_1257_;
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1314_, lean_object* v_p_u2082_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1314_, v_p_u2082_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
if (lean_obj_tag(v_m_1339_) == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
else
{
lean_object* v_p_1354_; lean_object* v_m_1355_; lean_object* v___x_1356_; 
v_p_1354_ = lean_ctor_get(v_m_1339_, 0);
lean_inc_ref(v_p_1354_);
v_m_1355_ = lean_ctor_get(v_m_1339_, 1);
lean_inc(v_m_1355_);
lean_dec_ref(v_m_1339_);
v___x_1356_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v_toRing_1358_; lean_object* v_vars_1359_; lean_object* v_x_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1428_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v_toRing_1358_ = lean_ctor_get(v_a_1357_, 0);
lean_inc_ref(v_toRing_1358_);
lean_dec(v_a_1357_);
v_vars_1359_ = lean_ctor_get(v_toRing_1358_, 14);
lean_inc_ref(v_vars_1359_);
lean_dec_ref(v_toRing_1358_);
v_x_1360_ = lean_ctor_get(v_p_1354_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_p_1354_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_p_1354_, 1);
lean_dec(v_unused_1429_);
v___x_1362_ = v_p_1354_;
v_isShared_1363_ = v_isSharedCheck_1428_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_x_1360_);
lean_dec(v_p_1354_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1428_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___y_1365_; lean_object* v_size_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_size_1423_ = lean_ctor_get(v_vars_1359_, 2);
v___x_1424_ = l_Lean_instInhabitedExpr;
v___x_1425_ = lean_nat_dec_lt(v_x_1360_, v_size_1423_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_vars_1359_);
v___x_1426_ = l_outOfBounds___redArg(v___x_1424_);
v___y_1365_ = v___x_1426_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1424_, v_vars_1359_, v_x_1360_);
lean_dec_ref(v_vars_1359_);
v___y_1365_ = v___x_1427_;
goto v___jp_1364_;
}
v___jp_1364_:
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = l_Lean_Expr_cleanupAnnotations(v___y_1365_);
v___x_1367_ = l_Lean_Expr_isApp(v___x_1366_);
if (v___x_1367_ == 0)
{
lean_dec_ref(v___x_1366_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v_arg_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_arg_1369_ = lean_ctor_get(v___x_1366_, 1);
lean_inc_ref(v_arg_1369_);
v___x_1370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1366_);
v___x_1371_ = l_Lean_Expr_isApp(v___x_1370_);
if (v___x_1371_ == 0)
{
lean_dec_ref(v___x_1370_);
lean_dec_ref(v_arg_1369_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1370_);
v___x_1374_ = l_Lean_Expr_isApp(v___x_1373_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_dec_ref(v_arg_1369_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1373_);
v___x_1377_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
v___x_1378_ = l_Lean_Expr_isConstOf(v___x_1376_, v___x_1377_);
lean_dec_ref(v___x_1376_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v_arg_1369_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = l_Lean_Expr_cleanupAnnotations(v_arg_1369_);
v___x_1381_ = l_Lean_Expr_isApp(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v___x_1380_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1380_);
v___x_1384_ = l_Lean_Expr_isApp(v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v___x_1383_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v_arg_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_arg_1386_ = lean_ctor_get(v___x_1383_, 1);
lean_inc_ref(v_arg_1386_);
v___x_1387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1383_);
v___x_1388_ = l_Lean_Expr_isApp(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_arg_1386_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1387_);
v___x_1391_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
v___x_1392_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1391_);
lean_dec_ref(v___x_1390_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v_arg_1386_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Meta_getNatValue_x3f(v_arg_1386_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
lean_dec_ref(v_arg_1386_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1414_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1414_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1414_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
if (lean_obj_tag(v_a_1395_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_m_1355_);
v_val_1399_ = lean_ctor_get(v_a_1395_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1395_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1401_ = v_a_1395_;
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_val_1399_);
lean_dec(v_a_1395_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v_x_1360_);
lean_ctor_set(v___x_1362_, 0, v_val_1399_);
v___x_1404_ = v___x_1362_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_val_1399_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_x_1360_);
v___x_1404_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1404_);
v___x_1406_ = v___x_1401_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1406_);
v___x_1408_ = v___x_1397_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
else
{
lean_del_object(v___x_1397_);
lean_dec(v_a_1395_);
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
v_m_1339_ = v_m_1355_;
goto _start;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1362_);
lean_dec(v_x_1360_);
lean_dec(v_m_1355_);
v_a_1415_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1394_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1394_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
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
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_m_1355_);
lean_dec_ref(v_p_1354_);
v_a_1430_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1356_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1356_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
if (lean_obj_tag(v_p_1452_) == 0)
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_isSharedCheck_1472_ = !lean_is_exclusive(v_p_1452_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_p_1452_, 0);
lean_dec(v_unused_1473_);
v___x_1466_ = v_p_1452_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_p_1452_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_box(0);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
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
else
{
lean_object* v_v_1474_; lean_object* v_p_1475_; lean_object* v___x_1476_; 
v_v_1474_ = lean_ctor_get(v_p_1452_, 1);
lean_inc(v_v_1474_);
v_p_1475_ = lean_ctor_get(v_p_1452_, 2);
lean_inc_ref(v_p_1475_);
lean_dec_ref(v_p_1452_);
v___x_1476_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_v_1474_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
if (lean_obj_tag(v_a_1477_) == 1)
{
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_p_1475_);
return v___x_1476_;
}
else
{
lean_dec(v_a_1477_);
lean_dec_ref(v___x_1476_);
v_p_1452_ = v_p_1475_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1475_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object* v_k_u2082_x27_1493_, lean_object* v_m_u2082_1494_, lean_object* v_p_u2082_1495_, lean_object* v_p_u2081_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
if (lean_obj_tag(v_p_u2081_1496_) == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref(v_p_u2081_1496_);
lean_dec_ref(v_p_u2082_1495_);
lean_dec(v_m_u2082_1494_);
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
else
{
lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v_p_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1649_; 
v_k_1511_ = lean_ctor_get(v_p_u2081_1496_, 0);
v_v_1512_ = lean_ctor_get(v_p_u2081_1496_, 1);
v_p_1513_ = lean_ctor_get(v_p_u2081_1496_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_p_u2081_1496_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1515_ = v_p_u2081_1496_;
v_isShared_1516_ = v_isSharedCheck_1649_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_p_1513_);
lean_inc(v_v_1512_);
lean_inc(v_k_1511_);
lean_dec(v_p_u2081_1496_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1649_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_1494_, v_v_1512_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
v___x_1518_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1493_, v_m_u2082_1494_, v_p_u2082_1495_, v_p_1513_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1601_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1601_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1601_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
if (lean_obj_tag(v_a_1519_) == 1)
{
lean_object* v_val_1523_; lean_object* v___x_1524_; 
lean_del_object(v___x_1521_);
v_val_1523_ = lean_ctor_get(v_a_1519_, 0);
lean_inc(v_val_1523_);
v___x_1524_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1588_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1588_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1588_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
if (lean_obj_tag(v_a_1525_) == 1)
{
lean_object* v_val_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1561_; 
v_val_1529_ = lean_ctor_get(v_a_1525_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_a_1525_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1531_ = v_a_1525_;
v_isShared_1532_ = v_isSharedCheck_1561_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_val_1529_);
lean_dec(v_a_1525_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1561_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_p_1533_; lean_object* v_k_u2081_1534_; lean_object* v_k_u2082_1535_; lean_object* v_m_u2082_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1560_; 
v_p_1533_ = lean_ctor_get(v_val_1523_, 0);
v_k_u2081_1534_ = lean_ctor_get(v_val_1523_, 1);
v_k_u2082_1535_ = lean_ctor_get(v_val_1523_, 2);
v_m_u2082_1536_ = lean_ctor_get(v_val_1523_, 3);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_val_1523_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1538_ = v_val_1523_;
v_isShared_1539_ = v_isSharedCheck_1560_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_m_u2082_1536_);
lean_inc(v_k_u2082_1535_);
lean_inc(v_k_u2081_1534_);
lean_inc(v_p_1533_);
lean_dec(v_val_1523_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1560_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1540_ = lean_int_mul(v_k_1511_, v_k_u2081_1534_);
lean_dec(v_k_1511_);
v___x_1541_ = lean_nat_to_int(v_val_1529_);
v___x_1542_ = lean_int_emod(v___x_1540_, v___x_1541_);
lean_dec(v___x_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1544_ = lean_int_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1546_; 
lean_dec_ref(v_a_1519_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 2, v_p_1533_);
lean_ctor_set(v___x_1515_, 0, v___x_1542_);
v___x_1546_ = v___x_1515_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_p_1533_);
v___x_1546_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1546_);
v___x_1548_ = v___x_1538_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_u2081_1534_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_k_u2082_1535_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_m_u2082_1536_);
v___x_1548_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1550_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1548_);
v___x_1550_ = v___x_1531_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1550_);
v___x_1552_ = v___x_1527_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec(v___x_1542_);
lean_del_object(v___x_1538_);
lean_dec(v_m_u2082_1536_);
lean_dec(v_k_u2082_1535_);
lean_dec(v_k_u2081_1534_);
lean_dec_ref(v_p_1533_);
lean_del_object(v___x_1531_);
lean_del_object(v___x_1515_);
lean_dec(v_v_1512_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_a_1519_);
v___x_1558_ = v___x_1527_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1519_);
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
}
else
{
lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1525_);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1519_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v_a_1519_, 0);
lean_dec(v_unused_1587_);
v___x_1563_ = v_a_1519_;
v_isShared_1564_ = v_isSharedCheck_1586_;
goto v_resetjp_1562_;
}
else
{
lean_dec(v_a_1519_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1586_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_p_1565_; lean_object* v_k_u2081_1566_; lean_object* v_k_u2082_1567_; lean_object* v_m_u2082_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1585_; 
v_p_1565_ = lean_ctor_get(v_val_1523_, 0);
v_k_u2081_1566_ = lean_ctor_get(v_val_1523_, 1);
v_k_u2082_1567_ = lean_ctor_get(v_val_1523_, 2);
v_m_u2082_1568_ = lean_ctor_get(v_val_1523_, 3);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_val_1523_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1570_ = v_val_1523_;
v_isShared_1571_ = v_isSharedCheck_1585_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_m_u2082_1568_);
lean_inc(v_k_u2082_1567_);
lean_inc(v_k_u2081_1566_);
lean_inc(v_p_1565_);
lean_dec(v_val_1523_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1585_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_int_mul(v_k_1511_, v_k_u2081_1566_);
lean_dec(v_k_1511_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 2, v_p_1565_);
lean_ctor_set(v___x_1515_, 0, v___x_1572_);
v___x_1574_ = v___x_1515_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_p_1565_);
v___x_1574_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1574_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_u2081_1566_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_k_u2082_1567_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_m_u2082_1568_);
v___x_1576_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1576_);
v___x_1578_ = v___x_1563_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1578_);
v___x_1580_ = v___x_1527_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
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
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_a_1519_);
lean_dec(v_val_1523_);
lean_del_object(v___x_1515_);
lean_dec(v_v_1512_);
lean_dec(v_k_1511_);
v_a_1589_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1524_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1524_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_dec(v_a_1519_);
lean_del_object(v___x_1515_);
lean_dec(v_v_1512_);
lean_dec(v_k_1511_);
v___x_1597_ = lean_box(0);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1597_);
v___x_1599_ = v___x_1521_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_del_object(v___x_1515_);
lean_dec(v_v_1512_);
lean_dec(v_k_1511_);
return v___x_1518_;
}
}
else
{
lean_object* v_m_u2082_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_g_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_k_u2082_1608_; lean_object* v___x_1609_; 
lean_del_object(v___x_1515_);
v_m_u2082_1602_ = l_Lean_Grind_CommRing_Mon_div(v_v_1512_, v_m_u2082_1494_);
v___x_1603_ = lean_nat_abs(v_k_1511_);
v___x_1604_ = lean_nat_abs(v_k_u2082_x27_1493_);
v_g_1605_ = lean_nat_gcd(v___x_1603_, v___x_1604_);
lean_dec(v___x_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_nat_to_int(v_g_1605_);
v___x_1607_ = lean_int_neg(v_k_1511_);
lean_dec(v_k_1511_);
v_k_u2082_1608_ = lean_int_ediv(v___x_1607_, v___x_1606_);
lean_dec(v___x_1607_);
lean_inc(v_m_u2082_1602_);
v___x_1609_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_u2082_1608_, v_m_u2082_1602_, v_p_u2082_1495_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v_k_u2081_1611_; lean_object* v___x_1612_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v_k_u2081_1611_ = lean_int_ediv(v_k_u2082_x27_1493_, v___x_1606_);
lean_dec(v___x_1606_);
v___x_1612_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_u2081_1611_, v_p_1513_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref(v___x_1612_);
lean_inc_ref(v_a_1506_);
v___x_1614_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1610_, v_a_1613_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1624_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1624_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1624_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1619_, 0, v_a_1615_);
lean_ctor_set(v___x_1619_, 1, v_k_u2081_1611_);
lean_ctor_set(v___x_1619_, 2, v_k_u2082_1608_);
lean_ctor_set(v___x_1619_, 3, v_m_u2082_1602_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_k_u2081_1611_);
lean_dec(v_k_u2082_1608_);
lean_dec(v_m_u2082_1602_);
v_a_1625_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1614_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1614_);
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
lean_dec(v_k_u2081_1611_);
lean_dec(v_a_1610_);
lean_dec(v_k_u2082_1608_);
lean_dec(v_m_u2082_1602_);
v_a_1633_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1612_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1612_);
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
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_k_u2082_1608_);
lean_dec(v___x_1606_);
lean_dec(v_m_u2082_1602_);
lean_dec_ref(v_p_1513_);
v_a_1641_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1609_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1609_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object* v_k_u2082_x27_1650_, lean_object* v_m_u2082_1651_, lean_object* v_p_u2082_1652_, lean_object* v_p_u2081_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1650_, v_m_u2082_1651_, v_p_u2082_1652_, v_p_u2081_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_k_u2082_x27_1650_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object* v_p_u2081_1667_, lean_object* v_p_u2082_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
if (lean_obj_tag(v_p_u2082_1668_) == 1)
{
lean_object* v_k_1681_; lean_object* v_v_1682_; lean_object* v_p_1683_; lean_object* v___x_1684_; 
v_k_1681_ = lean_ctor_get(v_p_u2082_1668_, 0);
lean_inc(v_k_1681_);
v_v_1682_ = lean_ctor_get(v_p_u2082_1668_, 1);
lean_inc(v_v_1682_);
v_p_1683_ = lean_ctor_get(v_p_u2082_1668_, 2);
lean_inc_ref(v_p_1683_);
lean_dec_ref(v_p_u2082_1668_);
v___x_1684_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1681_, v_v_1682_, v_p_1683_, v_p_u2081_1667_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_k_1681_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref(v_p_u2082_1668_);
lean_dec_ref(v_p_u2081_1667_);
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object* v_p_u2081_1687_, lean_object* v_p_u2082_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(v_p_u2081_1687_, v_p_u2082_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
return v_res_1701_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
