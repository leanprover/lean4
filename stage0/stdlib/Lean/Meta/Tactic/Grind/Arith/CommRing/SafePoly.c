// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM public import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly import Lean.Meta.Tactic.Grind.Arith.EvalNum import Init.Data.Nat.Linear
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_options_337_; lean_object* v_currRecDepth_338_; lean_object* v_maxRecDepth_339_; lean_object* v_ref_340_; lean_object* v_currNamespace_341_; lean_object* v_openDecls_342_; lean_object* v_initHeartbeats_343_; lean_object* v_maxHeartbeats_344_; lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; uint8_t v_diag_347_; lean_object* v_cancelTk_x3f_348_; uint8_t v_suppressElabErrors_349_; lean_object* v_inheritedTraceOptions_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_470_; 
v_fileName_335_ = lean_ctor_get(v_a_332_, 0);
v_fileMap_336_ = lean_ctor_get(v_a_332_, 1);
v_options_337_ = lean_ctor_get(v_a_332_, 2);
v_currRecDepth_338_ = lean_ctor_get(v_a_332_, 3);
v_maxRecDepth_339_ = lean_ctor_get(v_a_332_, 4);
v_ref_340_ = lean_ctor_get(v_a_332_, 5);
v_currNamespace_341_ = lean_ctor_get(v_a_332_, 6);
v_openDecls_342_ = lean_ctor_get(v_a_332_, 7);
v_initHeartbeats_343_ = lean_ctor_get(v_a_332_, 8);
v_maxHeartbeats_344_ = lean_ctor_get(v_a_332_, 9);
v_quotContext_345_ = lean_ctor_get(v_a_332_, 10);
v_currMacroScope_346_ = lean_ctor_get(v_a_332_, 11);
v_diag_347_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14);
v_cancelTk_x3f_348_ = lean_ctor_get(v_a_332_, 12);
v_suppressElabErrors_349_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_350_ = lean_ctor_get(v_a_332_, 13);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_470_ == 0)
{
v___x_352_ = v_a_332_;
v_isShared_353_ = v_isSharedCheck_470_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_inheritedTraceOptions_350_);
lean_inc(v_cancelTk_x3f_348_);
lean_inc(v_currMacroScope_346_);
lean_inc(v_quotContext_345_);
lean_inc(v_maxHeartbeats_344_);
lean_inc(v_initHeartbeats_343_);
lean_inc(v_openDecls_342_);
lean_inc(v_currNamespace_341_);
lean_inc(v_ref_340_);
lean_inc(v_maxRecDepth_339_);
lean_inc(v_currRecDepth_338_);
lean_inc(v_options_337_);
lean_inc(v_fileMap_336_);
lean_inc(v_fileName_335_);
lean_dec(v_a_332_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_470_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_eq(v_currRecDepth_338_, v_maxRecDepth_339_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_currRecDepth_338_, v___x_355_);
lean_dec(v_currRecDepth_338_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 3, v___x_356_);
v___x_358_ = v___x_352_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fileName_335_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_fileMap_336_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_options_337_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_maxRecDepth_339_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_ref_340_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_currNamespace_341_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_openDecls_342_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_initHeartbeats_343_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_maxHeartbeats_344_);
lean_ctor_set(v_reuseFailAlloc_468_, 10, v_quotContext_345_);
lean_ctor_set(v_reuseFailAlloc_468_, 11, v_currMacroScope_346_);
lean_ctor_set(v_reuseFailAlloc_468_, 12, v_cancelTk_x3f_348_);
lean_ctor_set(v_reuseFailAlloc_468_, 13, v_inheritedTraceOptions_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*14, v_diag_347_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*14 + 1, v_suppressElabErrors_349_);
v___x_358_ = v_reuseFailAlloc_468_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
if (lean_obj_tag(v_p_u2081_321_) == 0)
{
if (lean_obj_tag(v_p_u2082_322_) == 0)
{
lean_object* v_k_359_; lean_object* v_k_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_385_; 
v_k_359_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_inc(v_k_359_);
lean_dec_ref(v_p_u2081_321_);
v_k_360_ = lean_ctor_get(v_p_u2082_322_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_385_ == 0)
{
v___x_362_ = v_p_u2082_322_;
v_isShared_363_ = v_isSharedCheck_385_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_k_360_);
lean_dec(v_p_u2082_322_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_385_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_int_add(v_k_359_, v_k_360_);
lean_dec(v_k_360_);
lean_dec(v_k_359_);
v___x_365_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_364_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
lean_dec_ref(v___x_358_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_376_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_376_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_a_366_);
v___x_371_ = v___x_362_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_del_object(v___x_362_);
v_a_377_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_365_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_365_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
else
{
lean_object* v_k_386_; lean_object* v___x_387_; 
v_k_386_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_inc(v_k_386_);
lean_dec_ref(v_p_u2081_321_);
v___x_387_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2082_322_, v_k_386_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
lean_dec_ref(v___x_358_);
lean_dec(v_k_386_);
return v___x_387_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_322_) == 0)
{
lean_object* v_k_388_; lean_object* v___x_389_; 
v_k_388_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_inc(v_k_388_);
lean_dec_ref(v_p_u2082_322_);
v___x_389_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2081_321_, v_k_388_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
lean_dec_ref(v___x_358_);
lean_dec(v_k_388_);
return v___x_389_;
}
else
{
lean_object* v_k_390_; lean_object* v_v_391_; lean_object* v_p_392_; lean_object* v_k_393_; lean_object* v_v_394_; lean_object* v_p_395_; uint8_t v___x_396_; 
v_k_390_ = lean_ctor_get(v_p_u2081_321_, 0);
v_v_391_ = lean_ctor_get(v_p_u2081_321_, 1);
v_p_392_ = lean_ctor_get(v_p_u2081_321_, 2);
v_k_393_ = lean_ctor_get(v_p_u2082_322_, 0);
v_v_394_ = lean_ctor_get(v_p_u2082_322_, 1);
v_p_395_ = lean_ctor_get(v_p_u2082_322_, 2);
v___x_396_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_391_, v_v_394_);
switch(v___x_396_)
{
case 0:
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_412_; 
lean_inc_ref(v_p_395_);
lean_inc(v_v_394_);
lean_inc(v_k_393_);
v_isSharedCheck_412_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_413_ = lean_ctor_get(v_p_u2082_322_, 2);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_p_u2082_322_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_dec(v_unused_415_);
v___x_398_ = v_p_u2082_322_;
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
else
{
lean_dec(v_p_u2082_322_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_321_, v_p_395_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_411_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_411_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 2, v_a_401_);
v___x_406_ = v___x_398_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_k_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_v_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_a_401_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_del_object(v___x_398_);
lean_dec(v_v_394_);
lean_dec(v_k_393_);
return v___x_400_;
}
}
}
case 1:
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_445_; 
lean_inc_ref(v_p_395_);
lean_inc(v_k_393_);
lean_inc_ref(v_p_392_);
lean_inc(v_v_391_);
lean_inc(v_k_390_);
lean_dec_ref(v_p_u2081_321_);
v_isSharedCheck_445_ = !lean_is_exclusive(v_p_u2082_322_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_446_ = lean_ctor_get(v_p_u2082_322_, 2);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_p_u2082_322_, 1);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_p_u2082_322_, 0);
lean_dec(v_unused_448_);
v___x_417_ = v_p_u2082_322_;
v_isShared_418_ = v_isSharedCheck_445_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_p_u2082_322_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_445_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_int_add(v_k_390_, v_k_393_);
lean_dec(v_k_393_);
lean_dec(v_k_390_);
v___x_420_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_419_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref(v___x_420_);
v___x_422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_423_ = lean_int_dec_eq(v_a_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_392_, v_p_395_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_435_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_435_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 2, v_a_425_);
lean_ctor_set(v___x_417_, 1, v_v_391_);
lean_ctor_set(v___x_417_, 0, v_a_421_);
v___x_430_ = v___x_417_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_421_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_v_391_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_a_425_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_430_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_dec(v_a_421_);
lean_del_object(v___x_417_);
lean_dec(v_v_391_);
return v___x_424_;
}
}
else
{
lean_dec(v_a_421_);
lean_del_object(v___x_417_);
lean_dec(v_v_391_);
v_p_u2081_321_ = v_p_392_;
v_p_u2082_322_ = v_p_395_;
v_a_332_ = v___x_358_;
goto _start;
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_del_object(v___x_417_);
lean_dec_ref(v_p_395_);
lean_dec_ref(v_p_392_);
lean_dec(v_v_391_);
lean_dec_ref(v___x_358_);
v_a_437_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_420_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_420_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
default: 
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_464_; 
lean_inc_ref(v_p_392_);
lean_inc(v_v_391_);
lean_inc(v_k_390_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_p_u2081_321_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_465_ = lean_ctor_get(v_p_u2081_321_, 2);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_p_u2081_321_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_p_u2081_321_, 0);
lean_dec(v_unused_467_);
v___x_450_ = v_p_u2081_321_;
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_p_u2081_321_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; 
v___x_452_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_392_, v_p_u2082_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_358_, v_a_333_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_463_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_463_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 2, v_a_453_);
v___x_458_ = v___x_450_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_k_390_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_v_391_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_a_453_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
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
else
{
lean_del_object(v___x_450_);
lean_dec(v_v_391_);
lean_dec(v_k_390_);
return v___x_452_;
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
lean_object* v___x_469_; 
lean_del_object(v___x_352_);
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
v___x_469_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_340_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object* v_p_u2081_471_, lean_object* v_p_u2082_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_471_, v_p_u2082_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object* v_p_u2081_486_, lean_object* v_p_u2082_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_, lean_object* v_h__3_490_, lean_object* v_h__4_491_){
_start:
{
if (lean_obj_tag(v_p_u2081_486_) == 0)
{
lean_dec(v_h__4_491_);
lean_dec(v_h__3_490_);
if (lean_obj_tag(v_p_u2082_487_) == 0)
{
lean_object* v_k_492_; lean_object* v_k_493_; lean_object* v___x_494_; 
lean_dec(v_h__2_489_);
v_k_492_ = lean_ctor_get(v_p_u2081_486_, 0);
lean_inc(v_k_492_);
lean_dec_ref(v_p_u2081_486_);
v_k_493_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_493_);
lean_dec_ref(v_p_u2082_487_);
v___x_494_ = lean_apply_2(v_h__1_488_, v_k_492_, v_k_493_);
return v___x_494_;
}
else
{
lean_object* v_k_495_; lean_object* v_k_496_; lean_object* v_v_497_; lean_object* v_p_498_; lean_object* v___x_499_; 
lean_dec(v_h__1_488_);
v_k_495_ = lean_ctor_get(v_p_u2081_486_, 0);
lean_inc(v_k_495_);
lean_dec_ref(v_p_u2081_486_);
v_k_496_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_496_);
v_v_497_ = lean_ctor_get(v_p_u2082_487_, 1);
lean_inc(v_v_497_);
v_p_498_ = lean_ctor_get(v_p_u2082_487_, 2);
lean_inc_ref(v_p_498_);
lean_dec_ref(v_p_u2082_487_);
v___x_499_ = lean_apply_4(v_h__2_489_, v_k_495_, v_k_496_, v_v_497_, v_p_498_);
return v___x_499_;
}
}
else
{
lean_dec(v_h__2_489_);
lean_dec(v_h__1_488_);
if (lean_obj_tag(v_p_u2082_487_) == 0)
{
lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v_p_502_; lean_object* v_k_503_; lean_object* v___x_504_; 
lean_dec(v_h__4_491_);
v_k_500_ = lean_ctor_get(v_p_u2081_486_, 0);
lean_inc(v_k_500_);
v_v_501_ = lean_ctor_get(v_p_u2081_486_, 1);
lean_inc(v_v_501_);
v_p_502_ = lean_ctor_get(v_p_u2081_486_, 2);
lean_inc_ref(v_p_502_);
lean_dec_ref(v_p_u2081_486_);
v_k_503_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_503_);
lean_dec_ref(v_p_u2082_487_);
v___x_504_ = lean_apply_4(v_h__3_490_, v_k_500_, v_v_501_, v_p_502_, v_k_503_);
return v___x_504_;
}
else
{
lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v_p_507_; lean_object* v_k_508_; lean_object* v_v_509_; lean_object* v_p_510_; lean_object* v___x_511_; 
lean_dec(v_h__3_490_);
v_k_505_ = lean_ctor_get(v_p_u2081_486_, 0);
lean_inc(v_k_505_);
v_v_506_ = lean_ctor_get(v_p_u2081_486_, 1);
lean_inc(v_v_506_);
v_p_507_ = lean_ctor_get(v_p_u2081_486_, 2);
lean_inc_ref(v_p_507_);
lean_dec_ref(v_p_u2081_486_);
v_k_508_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_508_);
v_v_509_ = lean_ctor_get(v_p_u2082_487_, 1);
lean_inc(v_v_509_);
v_p_510_ = lean_ctor_get(v_p_u2082_487_, 2);
lean_inc_ref(v_p_510_);
lean_dec_ref(v_p_u2082_487_);
v___x_511_ = lean_apply_6(v_h__4_491_, v_k_505_, v_v_506_, v_p_507_, v_k_508_, v_v_509_, v_p_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object* v_motive_512_, lean_object* v_p_u2081_513_, lean_object* v_p_u2082_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_, lean_object* v_h__3_517_, lean_object* v_h__4_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(v_p_u2081_513_, v_p_u2082_514_, v_h__1_515_, v_h__2_516_, v_h__3_517_, v_h__4_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t v_x_520_, lean_object* v_h__1_521_, lean_object* v_h__2_522_, lean_object* v_h__3_523_){
_start:
{
switch(v_x_520_)
{
case 0:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_522_);
lean_dec(v_h__1_521_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_apply_1(v_h__3_523_, v___x_524_);
return v___x_525_;
}
case 1:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_h__3_523_);
lean_dec(v_h__2_522_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_apply_1(v_h__1_521_, v___x_526_);
return v___x_527_;
}
default: 
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_h__3_523_);
lean_dec(v_h__1_521_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_apply_1(v_h__2_522_, v___x_528_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object* v_x_530_, lean_object* v_h__1_531_, lean_object* v_h__2_532_, lean_object* v_h__3_533_){
_start:
{
uint8_t v_x_30__boxed_534_; lean_object* v_res_535_; 
v_x_30__boxed_534_ = lean_unbox(v_x_530_);
v_res_535_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_30__boxed_534_, v_h__1_531_, v_h__2_532_, v_h__3_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object* v_motive_536_, uint8_t v_x_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_, lean_object* v_h__3_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_537_, v_h__1_538_, v_h__2_539_, v_h__3_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object* v_motive_542_, lean_object* v_x_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_, lean_object* v_h__3_546_){
_start:
{
uint8_t v_x_45__boxed_547_; lean_object* v_res_548_; 
v_x_45__boxed_547_ = lean_unbox(v_x_543_);
v_res_548_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_542_, v_x_45__boxed_547_, v_h__1_544_, v_h__2_545_, v_h__3_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object* v_p_u2082_550_, lean_object* v_p_u2081_551_, lean_object* v_acc_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_fileName_565_; lean_object* v_fileMap_566_; lean_object* v_options_567_; lean_object* v_currRecDepth_568_; lean_object* v_maxRecDepth_569_; lean_object* v_ref_570_; lean_object* v_currNamespace_571_; lean_object* v_openDecls_572_; lean_object* v_initHeartbeats_573_; lean_object* v_maxHeartbeats_574_; lean_object* v_quotContext_575_; lean_object* v_currMacroScope_576_; uint8_t v_diag_577_; lean_object* v_cancelTk_x3f_578_; uint8_t v_suppressElabErrors_579_; lean_object* v_inheritedTraceOptions_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_613_; 
v_fileName_565_ = lean_ctor_get(v_a_562_, 0);
v_fileMap_566_ = lean_ctor_get(v_a_562_, 1);
v_options_567_ = lean_ctor_get(v_a_562_, 2);
v_currRecDepth_568_ = lean_ctor_get(v_a_562_, 3);
v_maxRecDepth_569_ = lean_ctor_get(v_a_562_, 4);
v_ref_570_ = lean_ctor_get(v_a_562_, 5);
v_currNamespace_571_ = lean_ctor_get(v_a_562_, 6);
v_openDecls_572_ = lean_ctor_get(v_a_562_, 7);
v_initHeartbeats_573_ = lean_ctor_get(v_a_562_, 8);
v_maxHeartbeats_574_ = lean_ctor_get(v_a_562_, 9);
v_quotContext_575_ = lean_ctor_get(v_a_562_, 10);
v_currMacroScope_576_ = lean_ctor_get(v_a_562_, 11);
v_diag_577_ = lean_ctor_get_uint8(v_a_562_, sizeof(void*)*14);
v_cancelTk_x3f_578_ = lean_ctor_get(v_a_562_, 12);
v_suppressElabErrors_579_ = lean_ctor_get_uint8(v_a_562_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_580_ = lean_ctor_get(v_a_562_, 13);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_562_);
if (v_isSharedCheck_613_ == 0)
{
v___x_582_ = v_a_562_;
v_isShared_583_ = v_isSharedCheck_613_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_inheritedTraceOptions_580_);
lean_inc(v_cancelTk_x3f_578_);
lean_inc(v_currMacroScope_576_);
lean_inc(v_quotContext_575_);
lean_inc(v_maxHeartbeats_574_);
lean_inc(v_initHeartbeats_573_);
lean_inc(v_openDecls_572_);
lean_inc(v_currNamespace_571_);
lean_inc(v_ref_570_);
lean_inc(v_maxRecDepth_569_);
lean_inc(v_currRecDepth_568_);
lean_inc(v_options_567_);
lean_inc(v_fileMap_566_);
lean_inc(v_fileName_565_);
lean_dec(v_a_562_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_613_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_eq(v_currRecDepth_568_, v_maxRecDepth_569_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v_currRecDepth_568_, v___x_585_);
lean_dec(v_currRecDepth_568_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 3, v___x_586_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_fileName_565_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_fileMap_566_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_options_567_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_maxRecDepth_569_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v_ref_570_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_currNamespace_571_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_openDecls_572_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v_initHeartbeats_573_);
lean_ctor_set(v_reuseFailAlloc_611_, 9, v_maxHeartbeats_574_);
lean_ctor_set(v_reuseFailAlloc_611_, 10, v_quotContext_575_);
lean_ctor_set(v_reuseFailAlloc_611_, 11, v_currMacroScope_576_);
lean_ctor_set(v_reuseFailAlloc_611_, 12, v_cancelTk_x3f_578_);
lean_ctor_set(v_reuseFailAlloc_611_, 13, v_inheritedTraceOptions_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*14, v_diag_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*14 + 1, v_suppressElabErrors_579_);
v___x_588_ = v_reuseFailAlloc_611_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
if (lean_obj_tag(v_p_u2081_551_) == 0)
{
lean_object* v_k_589_; lean_object* v___x_590_; 
v_k_589_ = lean_ctor_get(v_p_u2081_551_, 0);
lean_inc(v_k_589_);
lean_dec_ref(v_p_u2081_551_);
v___x_590_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_589_, v_p_u2082_550_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v___x_588_, v_a_563_);
lean_dec(v_k_589_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_590_);
v___x_592_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_552_, v_a_591_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v___x_588_, v_a_563_);
return v___x_592_;
}
else
{
lean_dec_ref(v___x_588_);
lean_dec_ref(v_acc_552_);
return v___x_590_;
}
}
else
{
lean_object* v_k_593_; lean_object* v_v_594_; lean_object* v_p_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_k_593_ = lean_ctor_get(v_p_u2081_551_, 0);
lean_inc(v_k_593_);
v_v_594_ = lean_ctor_get(v_p_u2081_551_, 1);
lean_inc(v_v_594_);
v_p_595_ = lean_ctor_get(v_p_u2081_551_, 2);
lean_inc_ref(v_p_595_);
lean_dec_ref(v_p_u2081_551_);
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
v___x_597_ = l_Lean_Core_checkSystem(v___x_596_, v___x_588_, v_a_563_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; 
lean_dec_ref(v___x_597_);
lean_inc_ref(v_p_u2082_550_);
v___x_598_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_593_, v_v_594_, v_p_u2082_550_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v___x_588_, v_a_563_);
lean_dec(v_k_593_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref(v___x_598_);
lean_inc_ref(v___x_588_);
v___x_600_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_552_, v_a_599_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v___x_588_, v_a_563_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref(v___x_600_);
v_p_u2081_551_ = v_p_595_;
v_acc_552_ = v_a_601_;
v_a_562_ = v___x_588_;
goto _start;
}
else
{
lean_dec_ref(v_p_595_);
lean_dec_ref(v___x_588_);
lean_dec_ref(v_p_u2082_550_);
return v___x_600_;
}
}
else
{
lean_dec_ref(v_p_595_);
lean_dec_ref(v___x_588_);
lean_dec_ref(v_acc_552_);
lean_dec_ref(v_p_u2082_550_);
return v___x_598_;
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_p_595_);
lean_dec(v_v_594_);
lean_dec(v_k_593_);
lean_dec_ref(v___x_588_);
lean_dec_ref(v_acc_552_);
lean_dec_ref(v_p_u2082_550_);
v_a_603_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_597_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_597_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
else
{
lean_object* v___x_612_; 
lean_del_object(v___x_582_);
lean_dec_ref(v_inheritedTraceOptions_580_);
lean_dec(v_cancelTk_x3f_578_);
lean_dec(v_currMacroScope_576_);
lean_dec(v_quotContext_575_);
lean_dec(v_maxHeartbeats_574_);
lean_dec(v_initHeartbeats_573_);
lean_dec(v_openDecls_572_);
lean_dec(v_currNamespace_571_);
lean_dec(v_maxRecDepth_569_);
lean_dec(v_currRecDepth_568_);
lean_dec_ref(v_options_567_);
lean_dec_ref(v_fileMap_566_);
lean_dec_ref(v_fileName_565_);
lean_dec_ref(v_acc_552_);
lean_dec_ref(v_p_u2081_551_);
lean_dec_ref(v_p_u2082_550_);
v___x_612_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_570_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object* v_p_u2082_614_, lean_object* v_p_u2081_615_, lean_object* v_acc_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_614_, v_p_u2081_615_, v_acc_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
return v_res_629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object* v_p_u2081_632_, lean_object* v_p_u2082_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_633_, v_p_u2081_632_, v___x_646_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object* v_p_u2081_648_, lean_object* v_p_u2082_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_648_, v_p_u2082_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
lean_dec(v_a_660_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
return v_res_662_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_to_int(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object* v_p_667_, lean_object* v_k_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_fileName_681_; lean_object* v_fileMap_682_; lean_object* v_options_683_; lean_object* v_currRecDepth_684_; lean_object* v_maxRecDepth_685_; lean_object* v_ref_686_; lean_object* v_currNamespace_687_; lean_object* v_openDecls_688_; lean_object* v_initHeartbeats_689_; lean_object* v_maxHeartbeats_690_; lean_object* v_quotContext_691_; lean_object* v_currMacroScope_692_; uint8_t v_diag_693_; lean_object* v_cancelTk_x3f_694_; uint8_t v_suppressElabErrors_695_; lean_object* v_inheritedTraceOptions_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_723_; 
v_fileName_681_ = lean_ctor_get(v_a_678_, 0);
v_fileMap_682_ = lean_ctor_get(v_a_678_, 1);
v_options_683_ = lean_ctor_get(v_a_678_, 2);
v_currRecDepth_684_ = lean_ctor_get(v_a_678_, 3);
v_maxRecDepth_685_ = lean_ctor_get(v_a_678_, 4);
v_ref_686_ = lean_ctor_get(v_a_678_, 5);
v_currNamespace_687_ = lean_ctor_get(v_a_678_, 6);
v_openDecls_688_ = lean_ctor_get(v_a_678_, 7);
v_initHeartbeats_689_ = lean_ctor_get(v_a_678_, 8);
v_maxHeartbeats_690_ = lean_ctor_get(v_a_678_, 9);
v_quotContext_691_ = lean_ctor_get(v_a_678_, 10);
v_currMacroScope_692_ = lean_ctor_get(v_a_678_, 11);
v_diag_693_ = lean_ctor_get_uint8(v_a_678_, sizeof(void*)*14);
v_cancelTk_x3f_694_ = lean_ctor_get(v_a_678_, 12);
v_suppressElabErrors_695_ = lean_ctor_get_uint8(v_a_678_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_696_ = lean_ctor_get(v_a_678_, 13);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_723_ == 0)
{
v___x_698_ = v_a_678_;
v_isShared_699_ = v_isSharedCheck_723_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_inheritedTraceOptions_696_);
lean_inc(v_cancelTk_x3f_694_);
lean_inc(v_currMacroScope_692_);
lean_inc(v_quotContext_691_);
lean_inc(v_maxHeartbeats_690_);
lean_inc(v_initHeartbeats_689_);
lean_inc(v_openDecls_688_);
lean_inc(v_currNamespace_687_);
lean_inc(v_ref_686_);
lean_inc(v_maxRecDepth_685_);
lean_inc(v_currRecDepth_684_);
lean_inc(v_options_683_);
lean_inc(v_fileMap_682_);
lean_inc(v_fileName_681_);
lean_dec(v_a_678_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_723_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_eq(v_currRecDepth_684_, v_maxRecDepth_685_);
if (v___x_700_ == 0)
{
lean_object* v_zero_701_; uint8_t v_isZero_702_; 
v_zero_701_ = lean_unsigned_to_nat(0u);
v_isZero_702_ = lean_nat_dec_eq(v_k_668_, v_zero_701_);
if (v_isZero_702_ == 1)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_inheritedTraceOptions_696_);
lean_dec(v_cancelTk_x3f_694_);
lean_dec(v_currMacroScope_692_);
lean_dec(v_quotContext_691_);
lean_dec(v_maxHeartbeats_690_);
lean_dec(v_initHeartbeats_689_);
lean_dec(v_openDecls_688_);
lean_dec(v_currNamespace_687_);
lean_dec(v_ref_686_);
lean_dec(v_maxRecDepth_685_);
lean_dec(v_currRecDepth_684_);
lean_dec_ref(v_options_683_);
lean_dec_ref(v_fileMap_682_);
lean_dec_ref(v_fileName_681_);
lean_dec_ref(v_p_667_);
v___x_703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
else
{
lean_object* v_one_705_; lean_object* v_n_706_; uint8_t v_isZero_707_; 
v_one_705_ = lean_unsigned_to_nat(1u);
v_n_706_ = lean_nat_sub(v_k_668_, v_one_705_);
v_isZero_707_ = lean_nat_dec_eq(v_n_706_, v_zero_701_);
if (v_isZero_707_ == 1)
{
lean_object* v___x_708_; 
lean_dec(v_n_706_);
lean_del_object(v___x_698_);
lean_dec_ref(v_inheritedTraceOptions_696_);
lean_dec(v_cancelTk_x3f_694_);
lean_dec(v_currMacroScope_692_);
lean_dec(v_quotContext_691_);
lean_dec(v_maxHeartbeats_690_);
lean_dec(v_initHeartbeats_689_);
lean_dec(v_openDecls_688_);
lean_dec(v_currNamespace_687_);
lean_dec(v_ref_686_);
lean_dec(v_maxRecDepth_685_);
lean_dec(v_currRecDepth_684_);
lean_dec_ref(v_options_683_);
lean_dec_ref(v_fileMap_682_);
lean_dec_ref(v_fileName_681_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_p_667_);
return v___x_708_;
}
else
{
lean_object* v_n_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v_n_709_ = lean_nat_sub(v_n_706_, v_one_705_);
lean_dec(v_n_706_);
v___x_710_ = lean_nat_add(v_currRecDepth_684_, v_one_705_);
lean_dec(v_currRecDepth_684_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 3, v___x_710_);
v___x_712_ = v___x_698_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fileName_681_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_fileMap_682_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_options_683_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_maxRecDepth_685_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_ref_686_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_currNamespace_687_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v_openDecls_688_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v_initHeartbeats_689_);
lean_ctor_set(v_reuseFailAlloc_721_, 9, v_maxHeartbeats_690_);
lean_ctor_set(v_reuseFailAlloc_721_, 10, v_quotContext_691_);
lean_ctor_set(v_reuseFailAlloc_721_, 11, v_currMacroScope_692_);
lean_ctor_set(v_reuseFailAlloc_721_, 12, v_cancelTk_x3f_694_);
lean_ctor_set(v_reuseFailAlloc_721_, 13, v_inheritedTraceOptions_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*14, v_diag_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*14 + 1, v_suppressElabErrors_695_);
v___x_712_ = v_reuseFailAlloc_721_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
uint8_t v_isZero_713_; 
v_isZero_713_ = lean_nat_dec_eq(v_n_709_, v_zero_701_);
if (v_isZero_713_ == 1)
{
lean_object* v___x_714_; 
lean_dec(v_n_709_);
lean_inc_ref(v_p_667_);
v___x_714_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_667_, v_p_667_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v___x_712_, v_a_679_);
return v___x_714_;
}
else
{
lean_object* v_n_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_n_715_ = lean_nat_sub(v_n_709_, v_one_705_);
lean_dec(v_n_709_);
v___x_716_ = lean_unsigned_to_nat(2u);
v___x_717_ = lean_nat_add(v_n_715_, v___x_716_);
lean_dec(v_n_715_);
lean_inc_ref(v___x_712_);
lean_inc_ref(v_p_667_);
v___x_718_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_667_, v___x_717_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v___x_712_, v_a_679_);
lean_dec(v___x_717_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_667_, v_a_719_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v___x_712_, v_a_679_);
return v___x_720_;
}
else
{
lean_dec_ref(v___x_712_);
lean_dec_ref(v_p_667_);
return v___x_718_;
}
}
}
}
}
}
else
{
lean_object* v___x_722_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_inheritedTraceOptions_696_);
lean_dec(v_cancelTk_x3f_694_);
lean_dec(v_currMacroScope_692_);
lean_dec(v_quotContext_691_);
lean_dec(v_maxHeartbeats_690_);
lean_dec(v_initHeartbeats_689_);
lean_dec(v_openDecls_688_);
lean_dec(v_currNamespace_687_);
lean_dec(v_maxRecDepth_685_);
lean_dec(v_currRecDepth_684_);
lean_dec_ref(v_options_683_);
lean_dec_ref(v_fileMap_682_);
lean_dec_ref(v_fileName_681_);
lean_dec_ref(v_p_667_);
v___x_722_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_686_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object* v_p_724_, lean_object* v_k_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_724_, v_k_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_k_725_);
return v_res_738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_740_ = lean_int_neg(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object* v_e_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_n_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; 
switch(lean_obj_tag(v_e_743_))
{
case 1:
{
lean_object* v_k_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_814_; 
v_k_788_ = lean_ctor_get(v_e_743_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_e_743_);
if (v_isSharedCheck_814_ == 0)
{
v___x_790_ = v_e_743_;
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_k_788_);
lean_dec(v_e_743_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_nat_to_int(v_k_788_);
v___x_793_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_792_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec_ref(v_a_753_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_805_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_805_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 0);
lean_ctor_set(v___x_790_, 0, v_a_794_);
v___x_799_ = v___x_790_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_804_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_800_);
v___x_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_del_object(v___x_790_);
v_a_806_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_793_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_793_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
case 3:
{
lean_object* v_i_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_a_753_);
v_i_815_ = lean_ctor_get(v_e_743_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_e_743_);
if (v_isSharedCheck_824_ == 0)
{
v___x_817_ = v_e_743_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_i_815_);
lean_dec(v_e_743_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 1);
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
case 4:
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_ctor_get(v_e_743_, 0);
lean_inc_ref(v_a_825_);
lean_dec_ref(v_e_743_);
lean_inc_ref(v_a_753_);
v___x_826_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_825_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
if (lean_obj_tag(v_a_827_) == 0)
{
lean_dec_ref(v_a_753_);
return v___x_826_;
}
else
{
lean_object* v_val_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v___x_826_);
v_val_828_ = lean_ctor_get(v_a_827_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_853_ == 0)
{
v___x_830_ = v_a_827_;
v_isShared_831_ = v_isSharedCheck_853_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_val_828_);
lean_dec(v_a_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_853_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_833_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_832_, v_val_828_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec_ref(v_a_753_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_844_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_844_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_a_834_);
v___x_839_ = v___x_830_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_del_object(v___x_830_);
v_a_845_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_833_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_833_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_753_);
return v___x_826_;
}
}
case 5:
{
lean_object* v_a_854_; lean_object* v_b_855_; lean_object* v___x_856_; 
v_a_854_ = lean_ctor_get(v_e_743_, 0);
lean_inc_ref(v_a_854_);
v_b_855_ = lean_ctor_get(v_e_743_, 1);
lean_inc_ref(v_b_855_);
lean_dec_ref(v_e_743_);
lean_inc_ref(v_a_753_);
v___x_856_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_854_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
if (lean_obj_tag(v_a_857_) == 0)
{
lean_dec_ref(v_b_855_);
lean_dec_ref(v_a_753_);
return v___x_856_;
}
else
{
lean_object* v_val_858_; lean_object* v___x_859_; 
lean_dec_ref(v___x_856_);
v_val_858_ = lean_ctor_get(v_a_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref(v_a_857_);
lean_inc_ref(v_a_753_);
v___x_859_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_855_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
if (lean_obj_tag(v_a_860_) == 0)
{
lean_dec(v_val_858_);
lean_dec_ref(v_a_753_);
return v___x_859_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___x_859_);
v_val_861_ = lean_ctor_get(v_a_860_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_885_ == 0)
{
v___x_863_ = v_a_860_;
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v_a_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_858_, v_val_861_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_876_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_a_866_);
v___x_871_ = v___x_863_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_del_object(v___x_863_);
v_a_877_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_865_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_865_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
else
{
lean_dec(v_val_858_);
lean_dec_ref(v_a_753_);
return v___x_859_;
}
}
}
else
{
lean_dec_ref(v_b_855_);
lean_dec_ref(v_a_753_);
return v___x_856_;
}
}
case 6:
{
lean_object* v_a_886_; lean_object* v_b_887_; lean_object* v___x_888_; 
v_a_886_ = lean_ctor_get(v_e_743_, 0);
lean_inc_ref(v_a_886_);
v_b_887_ = lean_ctor_get(v_e_743_, 1);
lean_inc_ref(v_b_887_);
lean_dec_ref(v_e_743_);
lean_inc_ref(v_a_753_);
v___x_888_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_886_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
if (lean_obj_tag(v_a_889_) == 0)
{
lean_dec_ref(v_b_887_);
lean_dec_ref(v_a_753_);
return v___x_888_;
}
else
{
lean_object* v_val_890_; lean_object* v___x_891_; 
lean_dec_ref(v___x_888_);
v_val_890_ = lean_ctor_get(v_a_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref(v_a_889_);
lean_inc_ref(v_a_753_);
v___x_891_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_887_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
if (lean_obj_tag(v_a_892_) == 0)
{
lean_dec(v_val_890_);
lean_dec_ref(v_a_753_);
return v___x_891_;
}
else
{
lean_object* v_val_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___x_891_);
v_val_893_ = lean_ctor_get(v_a_892_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_892_);
if (v_isSharedCheck_928_ == 0)
{
v___x_895_ = v_a_892_;
v_isShared_896_ = v_isSharedCheck_928_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_val_893_);
lean_dec(v_a_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_928_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_898_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_897_, v_val_893_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
v___x_900_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_890_, v_a_899_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_911_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_911_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v_a_901_);
v___x_906_ = v___x_895_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_906_);
v___x_908_ = v___x_903_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_895_);
v_a_912_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_900_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_900_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_del_object(v___x_895_);
lean_dec(v_val_890_);
lean_dec_ref(v_a_753_);
v_a_920_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_898_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_898_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
else
{
lean_dec(v_val_890_);
lean_dec_ref(v_a_753_);
return v___x_891_;
}
}
}
else
{
lean_dec_ref(v_b_887_);
lean_dec_ref(v_a_753_);
return v___x_888_;
}
}
case 7:
{
lean_object* v_a_929_; lean_object* v_b_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v_e_743_, 0);
lean_inc_ref(v_a_929_);
v_b_930_ = lean_ctor_get(v_e_743_, 1);
lean_inc_ref(v_b_930_);
lean_dec_ref(v_e_743_);
lean_inc_ref(v_a_753_);
v___x_931_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_929_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
if (lean_obj_tag(v_a_932_) == 0)
{
lean_dec_ref(v_b_930_);
lean_dec_ref(v_a_753_);
return v___x_931_;
}
else
{
lean_object* v_val_933_; lean_object* v___x_934_; 
lean_dec_ref(v___x_931_);
v_val_933_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref(v_a_932_);
lean_inc_ref(v_a_753_);
v___x_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_930_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
if (lean_obj_tag(v_a_935_) == 0)
{
lean_dec(v_val_933_);
lean_dec_ref(v_a_753_);
return v___x_934_;
}
else
{
lean_object* v_val_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___x_934_);
v_val_936_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_960_ == 0)
{
v___x_938_ = v_a_935_;
v_isShared_939_ = v_isSharedCheck_960_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_val_936_);
lean_dec(v_a_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_960_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; 
v___x_940_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_val_933_, v_val_936_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
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
lean_object* v___x_946_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_a_941_);
v___x_946_ = v___x_938_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_938_);
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
}
}
else
{
lean_dec(v_val_933_);
lean_dec_ref(v_a_753_);
return v___x_934_;
}
}
}
else
{
lean_dec_ref(v_b_930_);
lean_dec_ref(v_a_753_);
return v___x_931_;
}
}
case 8:
{
lean_object* v_a_961_; lean_object* v_k_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1058_; 
v_a_961_ = lean_ctor_get(v_e_743_, 0);
v_k_962_ = lean_ctor_get(v_e_743_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_e_743_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_964_ = v_e_743_;
v_isShared_965_ = v_isSharedCheck_1058_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_k_962_);
lean_inc(v_a_961_);
lean_dec(v_e_743_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1058_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_nat_dec_eq(v_k_962_, v___x_966_);
if (v___x_967_ == 0)
{
switch(lean_obj_tag(v_a_961_))
{
case 0:
{
lean_object* v_k_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1013_; 
lean_del_object(v___x_964_);
v_k_968_ = lean_ctor_get(v_a_961_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_970_ = v_a_961_;
v_isShared_971_ = v_isSharedCheck_1013_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_k_968_);
lean_dec(v_a_961_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1013_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; 
lean_inc(v_k_962_);
v___x_972_ = l_Lean_Meta_Grind_Arith_checkExp(v_k_962_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1004_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1004_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1004_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_a_973_) == 0)
{
if (v___x_967_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_del_object(v___x_970_);
lean_dec(v_k_968_);
lean_dec(v_k_962_);
lean_dec_ref(v_a_753_);
v___x_1000_ = lean_box(0);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_1000_);
v___x_1002_ = v___x_975_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_del_object(v___x_975_);
goto v___jp_977_;
}
}
else
{
lean_dec_ref(v_a_973_);
lean_del_object(v___x_975_);
goto v___jp_977_;
}
v___jp_977_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = l_Int_pow(v_k_968_, v_k_962_);
lean_dec(v_k_962_);
lean_dec(v_k_968_);
v___x_979_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_978_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec_ref(v_a_753_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_991_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_991_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_a_980_);
v___x_985_ = v___x_970_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_990_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_986_);
v___x_988_ = v___x_982_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_del_object(v___x_970_);
v_a_992_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_979_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_979_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_del_object(v___x_970_);
lean_dec(v_k_968_);
lean_dec(v_k_962_);
lean_dec_ref(v_a_753_);
v_a_1005_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_972_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_972_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v_a_753_);
v_i_1014_ = lean_ctor_get(v_a_961_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1016_ = v_a_961_;
v_isShared_1017_ = v_isSharedCheck_1028_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_i_1014_);
lean_dec(v_a_961_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1028_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 0);
lean_ctor_set(v___x_964_, 0, v_i_1014_);
v___x_1019_ = v___x_964_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_i_1014_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_k_962_);
v___x_1019_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_1021_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1022_);
v___x_1024_ = v___x_1016_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
}
default: 
{
lean_object* v___x_1029_; 
lean_del_object(v___x_964_);
lean_inc_ref(v_a_753_);
v___x_1029_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_961_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
if (lean_obj_tag(v_a_1030_) == 0)
{
lean_dec(v_k_962_);
lean_dec_ref(v_a_753_);
return v___x_1029_;
}
else
{
lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___x_1029_);
v_val_1031_ = lean_ctor_get(v_a_1030_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1030_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1033_ = v_a_1030_;
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_dec(v_a_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_1031_, v_k_962_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_k_962_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1046_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_a_1036_);
v___x_1041_ = v___x_1033_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1043_ = v___x_1038_;
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
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1033_);
v_a_1047_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1035_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1035_);
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
}
}
else
{
lean_dec(v_k_962_);
lean_dec_ref(v_a_753_);
return v___x_1029_;
}
}
}
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_del_object(v___x_964_);
lean_dec(v_k_962_);
lean_dec_ref(v_a_961_);
lean_dec_ref(v_a_753_);
v___x_1056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
default: 
{
lean_object* v_k_1059_; 
v_k_1059_ = lean_ctor_get(v_e_743_, 0);
lean_inc(v_k_1059_);
lean_dec_ref(v_e_743_);
v_n_757_ = v_k_1059_;
v___y_758_ = v_a_744_;
v___y_759_ = v_a_745_;
v___y_760_ = v_a_746_;
v___y_761_ = v_a_747_;
v___y_762_ = v_a_748_;
v___y_763_ = v_a_749_;
v___y_764_ = v_a_750_;
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
v___y_767_ = v_a_753_;
v___y_768_ = v_a_754_;
goto v___jp_756_;
}
}
v___jp_756_:
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_n_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v___y_767_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_779_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_a_770_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_a_780_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_769_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_769_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_1102_, lean_object* v_k_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1103_, v_p_1102_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_1117_, lean_object* v_k_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1117_, v_k_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_k_1118_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_1132_, lean_object* v_k_1133_, lean_object* v_m_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1133_, v_m_1134_, v_p_1132_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_1148_, lean_object* v_k_1149_, lean_object* v_m_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1148_, v_k_1149_, v_m_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_k_1149_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_1164_, lean_object* v_p_u2082_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_1164_, v_p_u2082_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_1179_, lean_object* v_p_u2082_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_1179_, v_p_u2082_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec(v_a_1191_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_1194_, lean_object* v_p_u2082_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_1194_, v_p_u2082_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1209_, lean_object* v_p_u2082_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1209_, v_p_u2082_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
return v_res_1223_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
v___x_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
lean_ctor_set(v___x_1227_, 2, v___x_1224_);
lean_ctor_set(v___x_1227_, 3, v___x_1225_);
lean_ctor_set(v___x_1227_, 4, v___x_1224_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1228_, lean_object* v_p_u2082_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
if (lean_obj_tag(v_p_u2081_1228_) == 1)
{
if (lean_obj_tag(v_p_u2082_1229_) == 1)
{
lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_p_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_p_1250_; lean_object* v_m_1251_; lean_object* v_m_u2081_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_g_1255_; lean_object* v___x_1256_; lean_object* v_c_u2081_1257_; lean_object* v___x_1258_; 
v_k_1245_ = lean_ctor_get(v_p_u2081_1228_, 0);
lean_inc(v_k_1245_);
v_v_1246_ = lean_ctor_get(v_p_u2081_1228_, 1);
lean_inc(v_v_1246_);
v_p_1247_ = lean_ctor_get(v_p_u2081_1228_, 2);
lean_inc_ref(v_p_1247_);
lean_dec_ref(v_p_u2081_1228_);
v_k_1248_ = lean_ctor_get(v_p_u2082_1229_, 0);
lean_inc(v_k_1248_);
v_v_1249_ = lean_ctor_get(v_p_u2082_1229_, 1);
lean_inc(v_v_1249_);
v_p_1250_ = lean_ctor_get(v_p_u2082_1229_, 2);
lean_inc_ref(v_p_1250_);
lean_dec_ref(v_p_u2082_1229_);
lean_inc(v_v_1249_);
lean_inc(v_v_1246_);
v_m_1251_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1246_, v_v_1249_);
lean_inc(v_m_1251_);
v_m_u2081_1252_ = l_Lean_Grind_CommRing_Mon_div(v_m_1251_, v_v_1246_);
v___x_1253_ = lean_nat_abs(v_k_1245_);
v___x_1254_ = lean_nat_abs(v_k_1248_);
v_g_1255_ = lean_nat_gcd(v___x_1253_, v___x_1254_);
lean_dec(v___x_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_nat_to_int(v_g_1255_);
v_c_u2081_1257_ = lean_int_ediv(v_k_1248_, v___x_1256_);
lean_dec(v_k_1248_);
lean_inc(v_m_u2081_1252_);
v___x_1258_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_1257_, v_m_u2081_1252_, v_p_1247_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v_m_u2082_1260_; lean_object* v___x_1261_; lean_object* v_c_u2082_1262_; lean_object* v___x_1263_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v_m_u2082_1260_ = l_Lean_Grind_CommRing_Mon_div(v_m_1251_, v_v_1249_);
v___x_1261_ = lean_int_neg(v_k_1245_);
lean_dec(v_k_1245_);
v_c_u2082_1262_ = lean_int_ediv(v___x_1261_, v___x_1256_);
lean_dec(v___x_1256_);
lean_dec(v___x_1261_);
lean_inc(v_m_u2082_1260_);
v___x_1263_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_1262_, v_m_u2082_1260_, v_p_1250_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1259_, v_a_1264_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1274_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1266_);
lean_ctor_set(v___x_1270_, 1, v_c_u2081_1257_);
lean_ctor_set(v___x_1270_, 2, v_m_u2081_1252_);
lean_ctor_set(v___x_1270_, 3, v_c_u2082_1262_);
lean_ctor_set(v___x_1270_, 4, v_m_u2082_1260_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_c_u2082_1262_);
lean_dec(v_m_u2082_1260_);
lean_dec(v_c_u2081_1257_);
lean_dec(v_m_u2081_1252_);
v_a_1275_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1265_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1265_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_c_u2082_1262_);
lean_dec(v_m_u2082_1260_);
lean_dec(v_a_1259_);
lean_dec(v_c_u2081_1257_);
lean_dec(v_m_u2081_1252_);
lean_dec_ref(v_a_1239_);
v_a_1283_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1263_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1263_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_c_u2081_1257_);
lean_dec(v___x_1256_);
lean_dec(v_m_u2081_1252_);
lean_dec(v_m_1251_);
lean_dec_ref(v_p_1250_);
lean_dec(v_v_1249_);
lean_dec(v_k_1245_);
lean_dec_ref(v_a_1239_);
v_a_1291_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1258_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1258_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_dec_ref(v_p_u2081_1228_);
lean_dec_ref(v_a_1239_);
lean_dec_ref(v_p_u2082_1229_);
goto v___jp_1242_;
}
}
else
{
lean_dec_ref(v_a_1239_);
lean_dec_ref(v_p_u2082_1229_);
lean_dec_ref(v_p_u2081_1228_);
goto v___jp_1242_;
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1299_, lean_object* v_p_u2082_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1299_, v_p_u2082_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
if (lean_obj_tag(v_m_1324_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
else
{
lean_object* v_p_1339_; lean_object* v_m_1340_; lean_object* v___x_1341_; 
v_p_1339_ = lean_ctor_get(v_m_1324_, 0);
lean_inc_ref(v_p_1339_);
v_m_1340_ = lean_ctor_get(v_m_1324_, 1);
lean_inc(v_m_1340_);
lean_dec_ref(v_m_1324_);
v___x_1341_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v_toRing_1343_; lean_object* v_vars_1344_; lean_object* v_x_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1413_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v_toRing_1343_ = lean_ctor_get(v_a_1342_, 0);
lean_inc_ref(v_toRing_1343_);
lean_dec(v_a_1342_);
v_vars_1344_ = lean_ctor_get(v_toRing_1343_, 14);
lean_inc_ref(v_vars_1344_);
lean_dec_ref(v_toRing_1343_);
v_x_1345_ = lean_ctor_get(v_p_1339_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_p_1339_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_p_1339_, 1);
lean_dec(v_unused_1414_);
v___x_1347_ = v_p_1339_;
v_isShared_1348_ = v_isSharedCheck_1413_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_x_1345_);
lean_dec(v_p_1339_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1413_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___y_1350_; lean_object* v_size_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_size_1408_ = lean_ctor_get(v_vars_1344_, 2);
v___x_1409_ = l_Lean_instInhabitedExpr;
v___x_1410_ = lean_nat_dec_lt(v_x_1345_, v_size_1408_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v_vars_1344_);
v___x_1411_ = l_outOfBounds___redArg(v___x_1409_);
v___y_1350_ = v___x_1411_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1409_, v_vars_1344_, v_x_1345_);
v___y_1350_ = v___x_1412_;
goto v___jp_1349_;
}
v___jp_1349_:
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = l_Lean_Expr_cleanupAnnotations(v___y_1350_);
v___x_1352_ = l_Lean_Expr_isApp(v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1351_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v_arg_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_arg_1354_ = lean_ctor_get(v___x_1351_, 1);
lean_inc_ref(v_arg_1354_);
v___x_1355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1351_);
v___x_1356_ = l_Lean_Expr_isApp(v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_arg_1354_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1355_);
v___x_1359_ = l_Lean_Expr_isApp(v___x_1358_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v___x_1358_);
lean_dec_ref(v_arg_1354_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1358_);
v___x_1362_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
v___x_1363_ = l_Lean_Expr_isConstOf(v___x_1361_, v___x_1362_);
lean_dec_ref(v___x_1361_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v_arg_1354_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = l_Lean_Expr_cleanupAnnotations(v_arg_1354_);
v___x_1366_ = l_Lean_Expr_isApp(v___x_1365_);
if (v___x_1366_ == 0)
{
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1365_);
v___x_1369_ = l_Lean_Expr_isApp(v___x_1368_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v___x_1368_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v_arg_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_arg_1371_ = lean_ctor_get(v___x_1368_, 1);
lean_inc_ref(v_arg_1371_);
v___x_1372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1368_);
v___x_1373_ = l_Lean_Expr_isApp(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec_ref(v___x_1372_);
lean_dec_ref(v_arg_1371_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1372_);
v___x_1376_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
v___x_1377_ = l_Lean_Expr_isConstOf(v___x_1375_, v___x_1376_);
lean_dec_ref(v___x_1375_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v_arg_1371_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
else
{
lean_object* v___x_1379_; 
lean_inc(v_a_1335_);
lean_inc_ref(v_a_1334_);
lean_inc(v_a_1333_);
lean_inc_ref(v_a_1332_);
v___x_1379_ = l_Lean_Meta_getNatValue_x3f(v_arg_1371_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec_ref(v_arg_1371_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1399_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1399_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1399_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_a_1380_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_m_1340_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
v_val_1384_ = lean_ctor_get(v_a_1380_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_a_1380_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1386_ = v_a_1380_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v_a_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v_x_1345_);
lean_ctor_set(v___x_1347_, 0, v_val_1384_);
v___x_1389_ = v___x_1347_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_val_1384_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_x_1345_);
v___x_1389_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1391_);
v___x_1393_ = v___x_1382_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
else
{
lean_del_object(v___x_1382_);
lean_dec(v_a_1380_);
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
v_m_1324_ = v_m_1340_;
goto _start;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1347_);
lean_dec(v_x_1345_);
lean_dec(v_m_1340_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
v_a_1400_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1379_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1379_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_m_1340_);
lean_dec_ref(v_p_1339_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
v_a_1415_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1341_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1341_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
if (lean_obj_tag(v_p_1437_) == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_p_1437_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_p_1437_, 0);
lean_dec(v_unused_1458_);
v___x_1451_ = v_p_1437_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_p_1437_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_box(0);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_v_1459_; lean_object* v_p_1460_; lean_object* v___x_1461_; 
v_v_1459_ = lean_ctor_get(v_p_1437_, 1);
lean_inc(v_v_1459_);
v_p_1460_ = lean_ctor_get(v_p_1437_, 2);
lean_inc_ref(v_p_1460_);
lean_dec_ref(v_p_1437_);
lean_inc(v_a_1448_);
lean_inc_ref(v_a_1447_);
lean_inc(v_a_1446_);
lean_inc_ref(v_a_1445_);
v___x_1461_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_v_1459_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
if (lean_obj_tag(v_a_1462_) == 1)
{
lean_dec_ref(v_a_1462_);
lean_dec_ref(v_p_1460_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
return v___x_1461_;
}
else
{
lean_dec_ref(v___x_1461_);
lean_dec(v_a_1462_);
v_p_1437_ = v_p_1460_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1460_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1477_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin);
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
