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
lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_options_337_; lean_object* v_currRecDepth_338_; lean_object* v_maxRecDepth_339_; lean_object* v_ref_340_; lean_object* v_currNamespace_341_; lean_object* v_openDecls_342_; lean_object* v_initHeartbeats_343_; lean_object* v_maxHeartbeats_344_; lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; uint8_t v_diag_347_; lean_object* v_cancelTk_x3f_348_; uint8_t v_suppressElabErrors_349_; lean_object* v_inheritedTraceOptions_350_; uint8_t v___x_351_; 
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
v___x_351_ = lean_nat_dec_eq(v_currRecDepth_338_, v_maxRecDepth_339_);
if (v___x_351_ == 0)
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
else
{
lean_object* v___x_464_; 
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
v___x_464_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_340_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object* v_p_u2081_465_, lean_object* v_p_u2082_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_465_, v_p_u2082_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object* v_p_u2081_480_, lean_object* v_p_u2082_481_, lean_object* v_h__1_482_, lean_object* v_h__2_483_, lean_object* v_h__3_484_, lean_object* v_h__4_485_){
_start:
{
if (lean_obj_tag(v_p_u2081_480_) == 0)
{
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
if (lean_obj_tag(v_p_u2082_481_) == 0)
{
lean_object* v_k_486_; lean_object* v_k_487_; lean_object* v___x_488_; 
lean_dec(v_h__2_483_);
v_k_486_ = lean_ctor_get(v_p_u2081_480_, 0);
lean_inc(v_k_486_);
lean_dec_ref(v_p_u2081_480_);
v_k_487_ = lean_ctor_get(v_p_u2082_481_, 0);
lean_inc(v_k_487_);
lean_dec_ref(v_p_u2082_481_);
v___x_488_ = lean_apply_2(v_h__1_482_, v_k_486_, v_k_487_);
return v___x_488_;
}
else
{
lean_object* v_k_489_; lean_object* v_k_490_; lean_object* v_v_491_; lean_object* v_p_492_; lean_object* v___x_493_; 
lean_dec(v_h__1_482_);
v_k_489_ = lean_ctor_get(v_p_u2081_480_, 0);
lean_inc(v_k_489_);
lean_dec_ref(v_p_u2081_480_);
v_k_490_ = lean_ctor_get(v_p_u2082_481_, 0);
lean_inc(v_k_490_);
v_v_491_ = lean_ctor_get(v_p_u2082_481_, 1);
lean_inc(v_v_491_);
v_p_492_ = lean_ctor_get(v_p_u2082_481_, 2);
lean_inc_ref(v_p_492_);
lean_dec_ref(v_p_u2082_481_);
v___x_493_ = lean_apply_4(v_h__2_483_, v_k_489_, v_k_490_, v_v_491_, v_p_492_);
return v___x_493_;
}
}
else
{
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
if (lean_obj_tag(v_p_u2082_481_) == 0)
{
lean_object* v_k_494_; lean_object* v_v_495_; lean_object* v_p_496_; lean_object* v_k_497_; lean_object* v___x_498_; 
lean_dec(v_h__4_485_);
v_k_494_ = lean_ctor_get(v_p_u2081_480_, 0);
lean_inc(v_k_494_);
v_v_495_ = lean_ctor_get(v_p_u2081_480_, 1);
lean_inc(v_v_495_);
v_p_496_ = lean_ctor_get(v_p_u2081_480_, 2);
lean_inc_ref(v_p_496_);
lean_dec_ref(v_p_u2081_480_);
v_k_497_ = lean_ctor_get(v_p_u2082_481_, 0);
lean_inc(v_k_497_);
lean_dec_ref(v_p_u2082_481_);
v___x_498_ = lean_apply_4(v_h__3_484_, v_k_494_, v_v_495_, v_p_496_, v_k_497_);
return v___x_498_;
}
else
{
lean_object* v_k_499_; lean_object* v_v_500_; lean_object* v_p_501_; lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v_p_504_; lean_object* v___x_505_; 
lean_dec(v_h__3_484_);
v_k_499_ = lean_ctor_get(v_p_u2081_480_, 0);
lean_inc(v_k_499_);
v_v_500_ = lean_ctor_get(v_p_u2081_480_, 1);
lean_inc(v_v_500_);
v_p_501_ = lean_ctor_get(v_p_u2081_480_, 2);
lean_inc_ref(v_p_501_);
lean_dec_ref(v_p_u2081_480_);
v_k_502_ = lean_ctor_get(v_p_u2082_481_, 0);
lean_inc(v_k_502_);
v_v_503_ = lean_ctor_get(v_p_u2082_481_, 1);
lean_inc(v_v_503_);
v_p_504_ = lean_ctor_get(v_p_u2082_481_, 2);
lean_inc_ref(v_p_504_);
lean_dec_ref(v_p_u2082_481_);
v___x_505_ = lean_apply_6(v_h__4_485_, v_k_499_, v_v_500_, v_p_501_, v_k_502_, v_v_503_, v_p_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object* v_motive_506_, lean_object* v_p_u2081_507_, lean_object* v_p_u2082_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_, lean_object* v_h__3_511_, lean_object* v_h__4_512_){
_start:
{
if (lean_obj_tag(v_p_u2081_507_) == 0)
{
lean_dec(v_h__4_512_);
lean_dec(v_h__3_511_);
if (lean_obj_tag(v_p_u2082_508_) == 0)
{
lean_object* v_k_513_; lean_object* v_k_514_; lean_object* v___x_515_; 
lean_dec(v_h__2_510_);
v_k_513_ = lean_ctor_get(v_p_u2081_507_, 0);
lean_inc(v_k_513_);
lean_dec_ref(v_p_u2081_507_);
v_k_514_ = lean_ctor_get(v_p_u2082_508_, 0);
lean_inc(v_k_514_);
lean_dec_ref(v_p_u2082_508_);
v___x_515_ = lean_apply_2(v_h__1_509_, v_k_513_, v_k_514_);
return v___x_515_;
}
else
{
lean_object* v_k_516_; lean_object* v_k_517_; lean_object* v_v_518_; lean_object* v_p_519_; lean_object* v___x_520_; 
lean_dec(v_h__1_509_);
v_k_516_ = lean_ctor_get(v_p_u2081_507_, 0);
lean_inc(v_k_516_);
lean_dec_ref(v_p_u2081_507_);
v_k_517_ = lean_ctor_get(v_p_u2082_508_, 0);
lean_inc(v_k_517_);
v_v_518_ = lean_ctor_get(v_p_u2082_508_, 1);
lean_inc(v_v_518_);
v_p_519_ = lean_ctor_get(v_p_u2082_508_, 2);
lean_inc_ref(v_p_519_);
lean_dec_ref(v_p_u2082_508_);
v___x_520_ = lean_apply_4(v_h__2_510_, v_k_516_, v_k_517_, v_v_518_, v_p_519_);
return v___x_520_;
}
}
else
{
lean_dec(v_h__2_510_);
lean_dec(v_h__1_509_);
if (lean_obj_tag(v_p_u2082_508_) == 0)
{
lean_object* v_k_521_; lean_object* v_v_522_; lean_object* v_p_523_; lean_object* v_k_524_; lean_object* v___x_525_; 
lean_dec(v_h__4_512_);
v_k_521_ = lean_ctor_get(v_p_u2081_507_, 0);
lean_inc(v_k_521_);
v_v_522_ = lean_ctor_get(v_p_u2081_507_, 1);
lean_inc(v_v_522_);
v_p_523_ = lean_ctor_get(v_p_u2081_507_, 2);
lean_inc_ref(v_p_523_);
lean_dec_ref(v_p_u2081_507_);
v_k_524_ = lean_ctor_get(v_p_u2082_508_, 0);
lean_inc(v_k_524_);
lean_dec_ref(v_p_u2082_508_);
v___x_525_ = lean_apply_4(v_h__3_511_, v_k_521_, v_v_522_, v_p_523_, v_k_524_);
return v___x_525_;
}
else
{
lean_object* v_k_526_; lean_object* v_v_527_; lean_object* v_p_528_; lean_object* v_k_529_; lean_object* v_v_530_; lean_object* v_p_531_; lean_object* v___x_532_; 
lean_dec(v_h__3_511_);
v_k_526_ = lean_ctor_get(v_p_u2081_507_, 0);
lean_inc(v_k_526_);
v_v_527_ = lean_ctor_get(v_p_u2081_507_, 1);
lean_inc(v_v_527_);
v_p_528_ = lean_ctor_get(v_p_u2081_507_, 2);
lean_inc_ref(v_p_528_);
lean_dec_ref(v_p_u2081_507_);
v_k_529_ = lean_ctor_get(v_p_u2082_508_, 0);
lean_inc(v_k_529_);
v_v_530_ = lean_ctor_get(v_p_u2082_508_, 1);
lean_inc(v_v_530_);
v_p_531_ = lean_ctor_get(v_p_u2082_508_, 2);
lean_inc_ref(v_p_531_);
lean_dec_ref(v_p_u2082_508_);
v___x_532_ = lean_apply_6(v_h__4_512_, v_k_526_, v_v_527_, v_p_528_, v_k_529_, v_v_530_, v_p_531_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t v_x_533_, lean_object* v_h__1_534_, lean_object* v_h__2_535_, lean_object* v_h__3_536_){
_start:
{
switch(v_x_533_)
{
case 0:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_h__2_535_);
lean_dec(v_h__1_534_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_apply_1(v_h__3_536_, v___x_537_);
return v___x_538_;
}
case 1:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_h__3_536_);
lean_dec(v_h__2_535_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_apply_1(v_h__1_534_, v___x_539_);
return v___x_540_;
}
default: 
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_h__3_536_);
lean_dec(v_h__1_534_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_apply_1(v_h__2_535_, v___x_541_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object* v_x_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_, lean_object* v_h__3_546_){
_start:
{
uint8_t v_x_36__boxed_547_; lean_object* v_res_548_; 
v_x_36__boxed_547_ = lean_unbox(v_x_543_);
v_res_548_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_36__boxed_547_, v_h__1_544_, v_h__2_545_, v_h__3_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object* v_motive_549_, uint8_t v_x_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_, lean_object* v_h__3_553_){
_start:
{
switch(v_x_550_)
{
case 0:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v_h__2_552_);
lean_dec(v_h__1_551_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_apply_1(v_h__3_553_, v___x_554_);
return v___x_555_;
}
case 1:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v_h__3_553_);
lean_dec(v_h__2_552_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_apply_1(v_h__1_551_, v___x_556_);
return v___x_557_;
}
default: 
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_h__3_553_);
lean_dec(v_h__1_551_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_apply_1(v_h__2_552_, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object* v_motive_560_, lean_object* v_x_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_, lean_object* v_h__3_564_){
_start:
{
uint8_t v_x_51__boxed_565_; lean_object* v_res_566_; 
v_x_51__boxed_565_ = lean_unbox(v_x_561_);
v_res_566_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_560_, v_x_51__boxed_565_, v_h__1_562_, v_h__2_563_, v_h__3_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object* v_p_u2082_568_, lean_object* v_p_u2081_569_, lean_object* v_acc_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_fileName_583_; lean_object* v_fileMap_584_; lean_object* v_options_585_; lean_object* v_currRecDepth_586_; lean_object* v_maxRecDepth_587_; lean_object* v_ref_588_; lean_object* v_currNamespace_589_; lean_object* v_openDecls_590_; lean_object* v_initHeartbeats_591_; lean_object* v_maxHeartbeats_592_; lean_object* v_quotContext_593_; lean_object* v_currMacroScope_594_; uint8_t v_diag_595_; lean_object* v_cancelTk_x3f_596_; uint8_t v_suppressElabErrors_597_; lean_object* v_inheritedTraceOptions_598_; uint8_t v___x_599_; 
v_fileName_583_ = lean_ctor_get(v_a_580_, 0);
lean_inc_ref(v_fileName_583_);
v_fileMap_584_ = lean_ctor_get(v_a_580_, 1);
lean_inc_ref(v_fileMap_584_);
v_options_585_ = lean_ctor_get(v_a_580_, 2);
lean_inc_ref(v_options_585_);
v_currRecDepth_586_ = lean_ctor_get(v_a_580_, 3);
lean_inc(v_currRecDepth_586_);
v_maxRecDepth_587_ = lean_ctor_get(v_a_580_, 4);
lean_inc(v_maxRecDepth_587_);
v_ref_588_ = lean_ctor_get(v_a_580_, 5);
lean_inc(v_ref_588_);
v_currNamespace_589_ = lean_ctor_get(v_a_580_, 6);
lean_inc(v_currNamespace_589_);
v_openDecls_590_ = lean_ctor_get(v_a_580_, 7);
lean_inc(v_openDecls_590_);
v_initHeartbeats_591_ = lean_ctor_get(v_a_580_, 8);
lean_inc(v_initHeartbeats_591_);
v_maxHeartbeats_592_ = lean_ctor_get(v_a_580_, 9);
lean_inc(v_maxHeartbeats_592_);
v_quotContext_593_ = lean_ctor_get(v_a_580_, 10);
lean_inc(v_quotContext_593_);
v_currMacroScope_594_ = lean_ctor_get(v_a_580_, 11);
lean_inc(v_currMacroScope_594_);
v_diag_595_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*14);
v_cancelTk_x3f_596_ = lean_ctor_get(v_a_580_, 12);
lean_inc(v_cancelTk_x3f_596_);
v_suppressElabErrors_597_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_598_ = lean_ctor_get(v_a_580_, 13);
lean_inc_ref(v_inheritedTraceOptions_598_);
lean_dec_ref(v_a_580_);
v___x_599_ = lean_nat_dec_eq(v_currRecDepth_586_, v_maxRecDepth_587_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_currRecDepth_586_, v___x_600_);
lean_dec(v_currRecDepth_586_);
v___x_602_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_602_, 0, v_fileName_583_);
lean_ctor_set(v___x_602_, 1, v_fileMap_584_);
lean_ctor_set(v___x_602_, 2, v_options_585_);
lean_ctor_set(v___x_602_, 3, v___x_601_);
lean_ctor_set(v___x_602_, 4, v_maxRecDepth_587_);
lean_ctor_set(v___x_602_, 5, v_ref_588_);
lean_ctor_set(v___x_602_, 6, v_currNamespace_589_);
lean_ctor_set(v___x_602_, 7, v_openDecls_590_);
lean_ctor_set(v___x_602_, 8, v_initHeartbeats_591_);
lean_ctor_set(v___x_602_, 9, v_maxHeartbeats_592_);
lean_ctor_set(v___x_602_, 10, v_quotContext_593_);
lean_ctor_set(v___x_602_, 11, v_currMacroScope_594_);
lean_ctor_set(v___x_602_, 12, v_cancelTk_x3f_596_);
lean_ctor_set(v___x_602_, 13, v_inheritedTraceOptions_598_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*14, v_diag_595_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*14 + 1, v_suppressElabErrors_597_);
if (lean_obj_tag(v_p_u2081_569_) == 0)
{
lean_object* v_k_603_; lean_object* v___x_604_; 
v_k_603_ = lean_ctor_get(v_p_u2081_569_, 0);
lean_inc(v_k_603_);
lean_dec_ref(v_p_u2081_569_);
v___x_604_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_603_, v_p_u2082_568_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v___x_602_, v_a_581_);
lean_dec(v_k_603_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref(v___x_604_);
v___x_606_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_570_, v_a_605_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v___x_602_, v_a_581_);
return v___x_606_;
}
else
{
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_570_);
return v___x_604_;
}
}
else
{
lean_object* v_k_607_; lean_object* v_v_608_; lean_object* v_p_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_k_607_ = lean_ctor_get(v_p_u2081_569_, 0);
lean_inc(v_k_607_);
v_v_608_ = lean_ctor_get(v_p_u2081_569_, 1);
lean_inc(v_v_608_);
v_p_609_ = lean_ctor_get(v_p_u2081_569_, 2);
lean_inc_ref(v_p_609_);
lean_dec_ref(v_p_u2081_569_);
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
v___x_611_ = l_Lean_Core_checkSystem(v___x_610_, v___x_602_, v_a_581_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v___x_611_);
lean_inc_ref(v_p_u2082_568_);
v___x_612_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_607_, v_v_608_, v_p_u2082_568_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v___x_602_, v_a_581_);
lean_dec(v_k_607_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref(v___x_612_);
lean_inc_ref(v___x_602_);
v___x_614_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_570_, v_a_613_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v___x_602_, v_a_581_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref(v___x_614_);
v_p_u2081_569_ = v_p_609_;
v_acc_570_ = v_a_615_;
v_a_580_ = v___x_602_;
goto _start;
}
else
{
lean_dec_ref(v_p_609_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v_p_u2082_568_);
return v___x_614_;
}
}
else
{
lean_dec_ref(v_p_609_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_570_);
lean_dec_ref(v_p_u2082_568_);
return v___x_612_;
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_p_609_);
lean_dec(v_v_608_);
lean_dec(v_k_607_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_570_);
lean_dec_ref(v_p_u2082_568_);
v_a_617_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_611_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_611_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v___x_625_; 
lean_dec_ref(v_inheritedTraceOptions_598_);
lean_dec(v_cancelTk_x3f_596_);
lean_dec(v_currMacroScope_594_);
lean_dec(v_quotContext_593_);
lean_dec(v_maxHeartbeats_592_);
lean_dec(v_initHeartbeats_591_);
lean_dec(v_openDecls_590_);
lean_dec(v_currNamespace_589_);
lean_dec(v_maxRecDepth_587_);
lean_dec(v_currRecDepth_586_);
lean_dec_ref(v_options_585_);
lean_dec_ref(v_fileMap_584_);
lean_dec_ref(v_fileName_583_);
lean_dec_ref(v_acc_570_);
lean_dec_ref(v_p_u2081_569_);
lean_dec_ref(v_p_u2082_568_);
v___x_625_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_588_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object* v_p_u2082_626_, lean_object* v_p_u2081_627_, lean_object* v_acc_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_626_, v_p_u2081_627_, v_acc_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_641_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object* v_p_u2081_644_, lean_object* v_p_u2082_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
lean_inc_ref(v_a_655_);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_645_, v_p_u2081_644_, v___x_658_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object* v_p_u2081_660_, lean_object* v_p_u2082_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_660_, v_p_u2082_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_nat_to_int(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object* v_p_679_, lean_object* v_k_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_fileName_693_; lean_object* v_fileMap_694_; lean_object* v_options_695_; lean_object* v_currRecDepth_696_; lean_object* v_maxRecDepth_697_; lean_object* v_ref_698_; lean_object* v_currNamespace_699_; lean_object* v_openDecls_700_; lean_object* v_initHeartbeats_701_; lean_object* v_maxHeartbeats_702_; lean_object* v_quotContext_703_; lean_object* v_currMacroScope_704_; uint8_t v_diag_705_; lean_object* v_cancelTk_x3f_706_; uint8_t v_suppressElabErrors_707_; lean_object* v_inheritedTraceOptions_708_; uint8_t v___x_709_; 
v_fileName_693_ = lean_ctor_get(v_a_690_, 0);
lean_inc_ref(v_fileName_693_);
v_fileMap_694_ = lean_ctor_get(v_a_690_, 1);
lean_inc_ref(v_fileMap_694_);
v_options_695_ = lean_ctor_get(v_a_690_, 2);
lean_inc_ref(v_options_695_);
v_currRecDepth_696_ = lean_ctor_get(v_a_690_, 3);
lean_inc(v_currRecDepth_696_);
v_maxRecDepth_697_ = lean_ctor_get(v_a_690_, 4);
lean_inc(v_maxRecDepth_697_);
v_ref_698_ = lean_ctor_get(v_a_690_, 5);
lean_inc(v_ref_698_);
v_currNamespace_699_ = lean_ctor_get(v_a_690_, 6);
lean_inc(v_currNamespace_699_);
v_openDecls_700_ = lean_ctor_get(v_a_690_, 7);
lean_inc(v_openDecls_700_);
v_initHeartbeats_701_ = lean_ctor_get(v_a_690_, 8);
lean_inc(v_initHeartbeats_701_);
v_maxHeartbeats_702_ = lean_ctor_get(v_a_690_, 9);
lean_inc(v_maxHeartbeats_702_);
v_quotContext_703_ = lean_ctor_get(v_a_690_, 10);
lean_inc(v_quotContext_703_);
v_currMacroScope_704_ = lean_ctor_get(v_a_690_, 11);
lean_inc(v_currMacroScope_704_);
v_diag_705_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*14);
v_cancelTk_x3f_706_ = lean_ctor_get(v_a_690_, 12);
lean_inc(v_cancelTk_x3f_706_);
v_suppressElabErrors_707_ = lean_ctor_get_uint8(v_a_690_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_708_ = lean_ctor_get(v_a_690_, 13);
lean_inc_ref(v_inheritedTraceOptions_708_);
lean_dec_ref(v_a_690_);
v___x_709_ = lean_nat_dec_eq(v_currRecDepth_696_, v_maxRecDepth_697_);
if (v___x_709_ == 0)
{
lean_object* v_zero_710_; uint8_t v_isZero_711_; 
v_zero_710_ = lean_unsigned_to_nat(0u);
v_isZero_711_ = lean_nat_dec_eq(v_k_680_, v_zero_710_);
if (v_isZero_711_ == 1)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v_inheritedTraceOptions_708_);
lean_dec(v_cancelTk_x3f_706_);
lean_dec(v_currMacroScope_704_);
lean_dec(v_quotContext_703_);
lean_dec(v_maxHeartbeats_702_);
lean_dec(v_initHeartbeats_701_);
lean_dec(v_openDecls_700_);
lean_dec(v_currNamespace_699_);
lean_dec(v_ref_698_);
lean_dec(v_maxRecDepth_697_);
lean_dec(v_currRecDepth_696_);
lean_dec_ref(v_options_695_);
lean_dec_ref(v_fileMap_694_);
lean_dec_ref(v_fileName_693_);
lean_dec_ref(v_p_679_);
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v_one_714_; lean_object* v_n_715_; uint8_t v_isZero_716_; 
v_one_714_ = lean_unsigned_to_nat(1u);
v_n_715_ = lean_nat_sub(v_k_680_, v_one_714_);
v_isZero_716_ = lean_nat_dec_eq(v_n_715_, v_zero_710_);
if (v_isZero_716_ == 1)
{
lean_object* v___x_717_; 
lean_dec(v_n_715_);
lean_dec_ref(v_inheritedTraceOptions_708_);
lean_dec(v_cancelTk_x3f_706_);
lean_dec(v_currMacroScope_704_);
lean_dec(v_quotContext_703_);
lean_dec(v_maxHeartbeats_702_);
lean_dec(v_initHeartbeats_701_);
lean_dec(v_openDecls_700_);
lean_dec(v_currNamespace_699_);
lean_dec(v_ref_698_);
lean_dec(v_maxRecDepth_697_);
lean_dec(v_currRecDepth_696_);
lean_dec_ref(v_options_695_);
lean_dec_ref(v_fileMap_694_);
lean_dec_ref(v_fileName_693_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_p_679_);
return v___x_717_;
}
else
{
lean_object* v_n_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v_isZero_721_; 
v_n_718_ = lean_nat_sub(v_n_715_, v_one_714_);
lean_dec(v_n_715_);
v___x_719_ = lean_nat_add(v_currRecDepth_696_, v_one_714_);
lean_dec(v_currRecDepth_696_);
v___x_720_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_720_, 0, v_fileName_693_);
lean_ctor_set(v___x_720_, 1, v_fileMap_694_);
lean_ctor_set(v___x_720_, 2, v_options_695_);
lean_ctor_set(v___x_720_, 3, v___x_719_);
lean_ctor_set(v___x_720_, 4, v_maxRecDepth_697_);
lean_ctor_set(v___x_720_, 5, v_ref_698_);
lean_ctor_set(v___x_720_, 6, v_currNamespace_699_);
lean_ctor_set(v___x_720_, 7, v_openDecls_700_);
lean_ctor_set(v___x_720_, 8, v_initHeartbeats_701_);
lean_ctor_set(v___x_720_, 9, v_maxHeartbeats_702_);
lean_ctor_set(v___x_720_, 10, v_quotContext_703_);
lean_ctor_set(v___x_720_, 11, v_currMacroScope_704_);
lean_ctor_set(v___x_720_, 12, v_cancelTk_x3f_706_);
lean_ctor_set(v___x_720_, 13, v_inheritedTraceOptions_708_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*14, v_diag_705_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*14 + 1, v_suppressElabErrors_707_);
v_isZero_721_ = lean_nat_dec_eq(v_n_718_, v_zero_710_);
if (v_isZero_721_ == 1)
{
lean_object* v___x_722_; 
lean_dec(v_n_718_);
lean_inc_ref(v_p_679_);
v___x_722_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_679_, v_p_679_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v___x_720_, v_a_691_);
lean_dec_ref(v___x_720_);
return v___x_722_;
}
else
{
lean_object* v_n_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_n_723_ = lean_nat_sub(v_n_718_, v_one_714_);
lean_dec(v_n_718_);
v___x_724_ = lean_unsigned_to_nat(2u);
v___x_725_ = lean_nat_add(v_n_723_, v___x_724_);
lean_dec(v_n_723_);
lean_inc_ref(v___x_720_);
lean_inc_ref(v_p_679_);
v___x_726_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_679_, v___x_725_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v___x_720_, v_a_691_);
lean_dec(v___x_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_726_);
v___x_728_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_679_, v_a_727_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v___x_720_, v_a_691_);
lean_dec_ref(v___x_720_);
return v___x_728_;
}
else
{
lean_dec_ref(v___x_720_);
lean_dec_ref(v_p_679_);
return v___x_726_;
}
}
}
}
}
else
{
lean_object* v___x_729_; 
lean_dec_ref(v_inheritedTraceOptions_708_);
lean_dec(v_cancelTk_x3f_706_);
lean_dec(v_currMacroScope_704_);
lean_dec(v_quotContext_703_);
lean_dec(v_maxHeartbeats_702_);
lean_dec(v_initHeartbeats_701_);
lean_dec(v_openDecls_700_);
lean_dec(v_currNamespace_699_);
lean_dec(v_maxRecDepth_697_);
lean_dec(v_currRecDepth_696_);
lean_dec_ref(v_options_695_);
lean_dec_ref(v_fileMap_694_);
lean_dec_ref(v_fileName_693_);
lean_dec_ref(v_p_679_);
v___x_729_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_698_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object* v_p_730_, lean_object* v_k_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_730_, v_k_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_k_731_);
return v_res_744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_746_ = lean_int_neg(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object* v_e_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_n_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; 
switch(lean_obj_tag(v_e_749_))
{
case 1:
{
lean_object* v_k_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_820_; 
v_k_794_ = lean_ctor_get(v_e_749_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_e_749_);
if (v_isSharedCheck_820_ == 0)
{
v___x_796_ = v_e_749_;
v_isShared_797_ = v_isSharedCheck_820_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_k_794_);
lean_dec(v_e_749_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_820_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_nat_to_int(v_k_794_);
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_798_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_811_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_811_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 0);
lean_ctor_set(v___x_796_, 0, v_a_800_);
v___x_805_ = v___x_796_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_810_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_796_);
v_a_812_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_799_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_799_);
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
case 3:
{
lean_object* v_i_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_830_; 
v_i_821_ = lean_ctor_get(v_e_749_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_e_749_);
if (v_isSharedCheck_830_ == 0)
{
v___x_823_ = v_e_749_;
v_isShared_824_ = v_isSharedCheck_830_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_i_821_);
lean_dec(v_e_749_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_830_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 1);
lean_ctor_set(v___x_823_, 0, v___x_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
case 4:
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_ctor_get(v_e_749_, 0);
lean_inc_ref(v_a_831_);
lean_dec_ref(v_e_749_);
v___x_832_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_831_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
if (lean_obj_tag(v_a_833_) == 0)
{
return v___x_832_;
}
else
{
lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___x_832_);
v_val_834_ = lean_ctor_get(v_a_833_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_859_ == 0)
{
v___x_836_ = v_a_833_;
v_isShared_837_ = v_isSharedCheck_859_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_dec(v_a_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_859_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_839_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_838_, v_val_834_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_850_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_850_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_a_840_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_del_object(v___x_836_);
v_a_851_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_839_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_839_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
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
}
}
else
{
return v___x_832_;
}
}
case 5:
{
lean_object* v_a_860_; lean_object* v_b_861_; lean_object* v___x_862_; 
v_a_860_ = lean_ctor_get(v_e_749_, 0);
lean_inc_ref(v_a_860_);
v_b_861_ = lean_ctor_get(v_e_749_, 1);
lean_inc_ref(v_b_861_);
lean_dec_ref(v_e_749_);
v___x_862_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_860_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
if (lean_obj_tag(v_a_863_) == 0)
{
lean_dec_ref(v_b_861_);
return v___x_862_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_865_; 
lean_dec_ref(v___x_862_);
v_val_864_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref(v_a_863_);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_861_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
if (lean_obj_tag(v_a_866_) == 0)
{
lean_dec(v_val_864_);
return v___x_865_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___x_865_);
v_val_867_ = lean_ctor_get(v_a_866_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_a_866_);
if (v_isSharedCheck_891_ == 0)
{
v___x_869_ = v_a_866_;
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v_a_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; 
lean_inc_ref(v_a_759_);
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_864_, v_val_867_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_882_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_882_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_a_872_);
v___x_877_ = v___x_869_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_877_);
v___x_879_ = v___x_874_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_del_object(v___x_869_);
v_a_883_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_871_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_871_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
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
}
}
else
{
lean_dec(v_val_864_);
return v___x_865_;
}
}
}
else
{
lean_dec_ref(v_b_861_);
return v___x_862_;
}
}
case 6:
{
lean_object* v_a_892_; lean_object* v_b_893_; lean_object* v___x_894_; 
v_a_892_ = lean_ctor_get(v_e_749_, 0);
lean_inc_ref(v_a_892_);
v_b_893_ = lean_ctor_get(v_e_749_, 1);
lean_inc_ref(v_b_893_);
lean_dec_ref(v_e_749_);
v___x_894_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_892_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
if (lean_obj_tag(v_a_895_) == 0)
{
lean_dec_ref(v_b_893_);
return v___x_894_;
}
else
{
lean_object* v_val_896_; lean_object* v___x_897_; 
lean_dec_ref(v___x_894_);
v_val_896_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref(v_a_895_);
v___x_897_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_893_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
if (lean_obj_tag(v_a_898_) == 0)
{
lean_dec(v_val_896_);
return v___x_897_;
}
else
{
lean_object* v_val_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___x_897_);
v_val_899_ = lean_ctor_get(v_a_898_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_934_ == 0)
{
v___x_901_ = v_a_898_;
v_isShared_902_ = v_isSharedCheck_934_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_val_899_);
lean_dec(v_a_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_934_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_903_, v_val_899_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
lean_inc_ref(v_a_759_);
v___x_906_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_896_, v_a_905_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_917_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v_a_907_);
v___x_912_ = v___x_901_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_901_);
v_a_918_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_906_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_906_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
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
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_del_object(v___x_901_);
lean_dec(v_val_896_);
v_a_926_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_904_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_904_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
else
{
lean_dec(v_val_896_);
return v___x_897_;
}
}
}
else
{
lean_dec_ref(v_b_893_);
return v___x_894_;
}
}
case 7:
{
lean_object* v_a_935_; lean_object* v_b_936_; lean_object* v___x_937_; 
v_a_935_ = lean_ctor_get(v_e_749_, 0);
lean_inc_ref(v_a_935_);
v_b_936_ = lean_ctor_get(v_e_749_, 1);
lean_inc_ref(v_b_936_);
lean_dec_ref(v_e_749_);
v___x_937_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_935_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
if (lean_obj_tag(v_a_938_) == 0)
{
lean_dec_ref(v_b_936_);
return v___x_937_;
}
else
{
lean_object* v_val_939_; lean_object* v___x_940_; 
lean_dec_ref(v___x_937_);
v_val_939_ = lean_ctor_get(v_a_938_, 0);
lean_inc(v_val_939_);
lean_dec_ref(v_a_938_);
v___x_940_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_936_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
if (lean_obj_tag(v_a_941_) == 0)
{
lean_dec(v_val_939_);
return v___x_940_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___x_940_);
v_val_942_ = lean_ctor_get(v_a_941_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_941_);
if (v_isSharedCheck_966_ == 0)
{
v___x_944_ = v_a_941_;
v_isShared_945_ = v_isSharedCheck_966_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_a_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_966_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_val_939_, v_val_942_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_957_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_957_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_a_947_);
v___x_952_ = v___x_944_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_del_object(v___x_944_);
v_a_958_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_946_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_946_);
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
}
}
else
{
lean_dec(v_val_939_);
return v___x_940_;
}
}
}
else
{
lean_dec_ref(v_b_936_);
return v___x_937_;
}
}
case 8:
{
lean_object* v_a_967_; lean_object* v_k_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1064_; 
v_a_967_ = lean_ctor_get(v_e_749_, 0);
v_k_968_ = lean_ctor_get(v_e_749_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_e_749_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_970_ = v_e_749_;
v_isShared_971_ = v_isSharedCheck_1064_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_k_968_);
lean_inc(v_a_967_);
lean_dec(v_e_749_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1064_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_nat_dec_eq(v_k_968_, v___x_972_);
if (v___x_973_ == 0)
{
switch(lean_obj_tag(v_a_967_))
{
case 0:
{
lean_object* v_k_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_970_);
v_k_974_ = lean_ctor_get(v_a_967_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_976_ = v_a_967_;
v_isShared_977_ = v_isSharedCheck_1019_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_k_974_);
lean_dec(v_a_967_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1019_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; 
lean_inc(v_k_968_);
v___x_978_ = l_Lean_Meta_Grind_Arith_checkExp(v_k_968_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1010_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_1010_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1010_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
if (lean_obj_tag(v_a_979_) == 0)
{
if (v___x_973_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_del_object(v___x_976_);
lean_dec(v_k_974_);
lean_dec(v_k_968_);
v___x_1006_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_1006_);
v___x_1008_ = v___x_981_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_del_object(v___x_981_);
goto v___jp_983_;
}
}
else
{
lean_dec_ref(v_a_979_);
lean_del_object(v___x_981_);
goto v___jp_983_;
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = l_Int_pow(v_k_974_, v_k_968_);
lean_dec(v_k_968_);
lean_dec(v_k_974_);
v___x_985_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_984_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_997_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_997_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v_a_986_);
v___x_991_ = v___x_976_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_996_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_992_);
v___x_994_ = v___x_988_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_del_object(v___x_976_);
v_a_998_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_985_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_985_);
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
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_976_);
lean_dec(v_k_974_);
lean_dec(v_k_968_);
v_a_1011_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_978_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_978_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1034_; 
v_i_1020_ = lean_ctor_get(v_a_967_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1022_ = v_a_967_;
v_isShared_1023_ = v_isSharedCheck_1034_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_i_1020_);
lean_dec(v_a_967_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1034_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 0);
lean_ctor_set(v___x_970_, 0, v_i_1020_);
v___x_1025_ = v___x_970_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_i_1020_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_968_);
v___x_1025_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_1027_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1028_);
v___x_1030_ = v___x_1022_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
}
}
default: 
{
lean_object* v___x_1035_; 
lean_del_object(v___x_970_);
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_967_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
if (lean_obj_tag(v_a_1036_) == 0)
{
lean_dec(v_k_968_);
return v___x_1035_;
}
else
{
lean_object* v_val_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___x_1035_);
v_val_1037_ = lean_ctor_get(v_a_1036_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_a_1036_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1039_ = v_a_1036_;
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_val_1037_);
lean_dec(v_a_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; 
lean_inc_ref(v_a_759_);
v___x_1041_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_1037_, v_k_968_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_k_968_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1052_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_a_1042_);
v___x_1047_ = v___x_1039_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1047_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_del_object(v___x_1039_);
v_a_1053_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1041_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1041_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
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
}
}
else
{
lean_dec(v_k_968_);
return v___x_1035_;
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_del_object(v___x_970_);
lean_dec(v_k_968_);
lean_dec_ref(v_a_967_);
v___x_1062_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
default: 
{
lean_object* v_k_1065_; 
v_k_1065_ = lean_ctor_get(v_e_749_, 0);
lean_inc(v_k_1065_);
lean_dec_ref(v_e_749_);
v_n_763_ = v_k_1065_;
v___y_764_ = v_a_750_;
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
v___y_767_ = v_a_753_;
v___y_768_ = v_a_754_;
v___y_769_ = v_a_755_;
v___y_770_ = v_a_756_;
v___y_771_ = v_a_757_;
v___y_772_ = v_a_758_;
v___y_773_ = v_a_759_;
v___y_774_ = v_a_760_;
goto v___jp_762_;
}
}
v___jp_762_:
{
lean_object* v___x_775_; 
v___x_775_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_n_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_785_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_785_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_a_776_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_775_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_775_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_1108_, lean_object* v_k_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1109_, v_p_1108_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_1123_, lean_object* v_k_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1123_, v_k_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_k_1124_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_1138_, lean_object* v_k_1139_, lean_object* v_m_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1139_, v_m_1140_, v_p_1138_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_1154_, lean_object* v_k_1155_, lean_object* v_m_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1154_, v_k_1155_, v_m_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_k_1155_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_1170_, lean_object* v_p_u2082_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_1170_, v_p_u2082_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_1185_, lean_object* v_p_u2082_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_1185_, v_p_u2082_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_1200_, lean_object* v_p_u2082_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; 
lean_inc_ref(v_a_1211_);
v___x_1214_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_1200_, v_p_u2082_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1215_, lean_object* v_p_u2082_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1215_, v_p_u2082_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1229_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
v___x_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1231_);
lean_ctor_set(v___x_1233_, 2, v___x_1230_);
lean_ctor_set(v___x_1233_, 3, v___x_1231_);
lean_ctor_set(v___x_1233_, 4, v___x_1230_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1234_, lean_object* v_p_u2082_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
if (lean_obj_tag(v_p_u2081_1234_) == 1)
{
if (lean_obj_tag(v_p_u2082_1235_) == 1)
{
lean_object* v_k_1251_; lean_object* v_v_1252_; lean_object* v_p_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_p_1256_; lean_object* v_m_1257_; lean_object* v_m_u2081_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_g_1261_; lean_object* v___x_1262_; lean_object* v_c_u2081_1263_; lean_object* v___x_1264_; 
v_k_1251_ = lean_ctor_get(v_p_u2081_1234_, 0);
lean_inc(v_k_1251_);
v_v_1252_ = lean_ctor_get(v_p_u2081_1234_, 1);
lean_inc(v_v_1252_);
v_p_1253_ = lean_ctor_get(v_p_u2081_1234_, 2);
lean_inc_ref(v_p_1253_);
lean_dec_ref(v_p_u2081_1234_);
v_k_1254_ = lean_ctor_get(v_p_u2082_1235_, 0);
lean_inc(v_k_1254_);
v_v_1255_ = lean_ctor_get(v_p_u2082_1235_, 1);
lean_inc(v_v_1255_);
v_p_1256_ = lean_ctor_get(v_p_u2082_1235_, 2);
lean_inc_ref(v_p_1256_);
lean_dec_ref(v_p_u2082_1235_);
lean_inc(v_v_1255_);
lean_inc(v_v_1252_);
v_m_1257_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1252_, v_v_1255_);
lean_inc(v_m_1257_);
v_m_u2081_1258_ = l_Lean_Grind_CommRing_Mon_div(v_m_1257_, v_v_1252_);
v___x_1259_ = lean_nat_abs(v_k_1251_);
v___x_1260_ = lean_nat_abs(v_k_1254_);
v_g_1261_ = lean_nat_gcd(v___x_1259_, v___x_1260_);
lean_dec(v___x_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_nat_to_int(v_g_1261_);
v_c_u2081_1263_ = lean_int_ediv(v_k_1254_, v___x_1262_);
lean_dec(v_k_1254_);
lean_inc(v_m_u2081_1258_);
v___x_1264_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_1263_, v_m_u2081_1258_, v_p_1253_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v_m_u2082_1266_; lean_object* v___x_1267_; lean_object* v_c_u2082_1268_; lean_object* v___x_1269_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v_m_u2082_1266_ = l_Lean_Grind_CommRing_Mon_div(v_m_1257_, v_v_1255_);
v___x_1267_ = lean_int_neg(v_k_1251_);
lean_dec(v_k_1251_);
v_c_u2082_1268_ = lean_int_ediv(v___x_1267_, v___x_1262_);
lean_dec(v___x_1262_);
lean_dec(v___x_1267_);
lean_inc(v_m_u2082_1266_);
v___x_1269_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_1268_, v_m_u2082_1266_, v_p_1256_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
lean_inc_ref(v_a_1245_);
v___x_1271_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1265_, v_a_1270_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1272_);
lean_ctor_set(v___x_1276_, 1, v_c_u2081_1263_);
lean_ctor_set(v___x_1276_, 2, v_m_u2081_1258_);
lean_ctor_set(v___x_1276_, 3, v_c_u2082_1268_);
lean_ctor_set(v___x_1276_, 4, v_m_u2082_1266_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
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
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_c_u2082_1268_);
lean_dec(v_m_u2082_1266_);
lean_dec(v_c_u2081_1263_);
lean_dec(v_m_u2081_1258_);
v_a_1281_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1271_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1271_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_c_u2082_1268_);
lean_dec(v_m_u2082_1266_);
lean_dec(v_a_1265_);
lean_dec(v_c_u2081_1263_);
lean_dec(v_m_u2081_1258_);
v_a_1289_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1269_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1269_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_c_u2081_1263_);
lean_dec(v___x_1262_);
lean_dec(v_m_u2081_1258_);
lean_dec(v_m_1257_);
lean_dec_ref(v_p_1256_);
lean_dec(v_v_1255_);
lean_dec(v_k_1251_);
v_a_1297_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1264_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1264_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_dec_ref(v_p_u2081_1234_);
lean_dec_ref(v_p_u2082_1235_);
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v_p_u2082_1235_);
lean_dec_ref(v_p_u2081_1234_);
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1305_, lean_object* v_p_u2082_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1305_, v_p_u2082_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
if (lean_obj_tag(v_m_1330_) == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
else
{
lean_object* v_p_1345_; lean_object* v_m_1346_; lean_object* v___x_1347_; 
v_p_1345_ = lean_ctor_get(v_m_1330_, 0);
lean_inc_ref(v_p_1345_);
v_m_1346_ = lean_ctor_get(v_m_1330_, 1);
lean_inc(v_m_1346_);
lean_dec_ref(v_m_1330_);
v___x_1347_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_toRing_1349_; lean_object* v_vars_1350_; lean_object* v_x_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1419_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v_toRing_1349_ = lean_ctor_get(v_a_1348_, 0);
lean_inc_ref(v_toRing_1349_);
lean_dec(v_a_1348_);
v_vars_1350_ = lean_ctor_get(v_toRing_1349_, 14);
lean_inc_ref(v_vars_1350_);
lean_dec_ref(v_toRing_1349_);
v_x_1351_ = lean_ctor_get(v_p_1345_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_p_1345_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v_p_1345_, 1);
lean_dec(v_unused_1420_);
v___x_1353_ = v_p_1345_;
v_isShared_1354_ = v_isSharedCheck_1419_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_x_1351_);
lean_dec(v_p_1345_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1419_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___y_1356_; lean_object* v_size_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_size_1414_ = lean_ctor_get(v_vars_1350_, 2);
v___x_1415_ = l_Lean_instInhabitedExpr;
v___x_1416_ = lean_nat_dec_lt(v_x_1351_, v_size_1414_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref(v_vars_1350_);
v___x_1417_ = l_outOfBounds___redArg(v___x_1415_);
v___y_1356_ = v___x_1417_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1415_, v_vars_1350_, v_x_1351_);
v___y_1356_ = v___x_1418_;
goto v___jp_1355_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = l_Lean_Expr_cleanupAnnotations(v___y_1356_);
v___x_1358_ = l_Lean_Expr_isApp(v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v___x_1357_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v_arg_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_arg_1360_ = lean_ctor_get(v___x_1357_, 1);
lean_inc_ref(v_arg_1360_);
v___x_1361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1357_);
v___x_1362_ = l_Lean_Expr_isApp(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v___x_1361_);
lean_dec_ref(v_arg_1360_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1361_);
v___x_1365_ = l_Lean_Expr_isApp(v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v_arg_1360_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1364_);
v___x_1368_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
v___x_1369_ = l_Lean_Expr_isConstOf(v___x_1367_, v___x_1368_);
lean_dec_ref(v___x_1367_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v_arg_1360_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = l_Lean_Expr_cleanupAnnotations(v_arg_1360_);
v___x_1372_ = l_Lean_Expr_isApp(v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v___x_1371_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1371_);
v___x_1375_ = l_Lean_Expr_isApp(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec_ref(v___x_1374_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v_arg_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_arg_1377_ = lean_ctor_get(v___x_1374_, 1);
lean_inc_ref(v_arg_1377_);
v___x_1378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1374_);
v___x_1379_ = l_Lean_Expr_isApp(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v___x_1378_);
lean_dec_ref(v_arg_1377_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1378_);
v___x_1382_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
v___x_1383_ = l_Lean_Expr_isConstOf(v___x_1381_, v___x_1382_);
lean_dec_ref(v___x_1381_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_arg_1377_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
else
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_getNatValue_x3f(v_arg_1377_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
lean_dec_ref(v_arg_1377_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1405_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1405_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1405_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
if (lean_obj_tag(v_a_1386_) == 1)
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_m_1346_);
v_val_1390_ = lean_ctor_get(v_a_1386_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_a_1386_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1392_ = v_a_1386_;
v_isShared_1393_ = v_isSharedCheck_1403_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v_a_1386_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1403_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_x_1351_);
lean_ctor_set(v___x_1353_, 0, v_val_1390_);
v___x_1395_ = v___x_1353_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_val_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_x_1351_);
v___x_1395_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1395_);
v___x_1397_ = v___x_1392_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1397_);
v___x_1399_ = v___x_1388_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
else
{
lean_del_object(v___x_1388_);
lean_dec(v_a_1386_);
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
v_m_1330_ = v_m_1346_;
goto _start;
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1353_);
lean_dec(v_x_1351_);
lean_dec(v_m_1346_);
v_a_1406_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1385_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1385_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
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
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_m_1346_);
lean_dec_ref(v_p_1345_);
v_a_1421_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1347_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1347_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
if (lean_obj_tag(v_p_1443_) == 0)
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v_p_1443_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_p_1443_, 0);
lean_dec(v_unused_1464_);
v___x_1457_ = v_p_1443_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_p_1443_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_v_1465_; lean_object* v_p_1466_; lean_object* v___x_1467_; 
v_v_1465_ = lean_ctor_get(v_p_1443_, 1);
lean_inc(v_v_1465_);
v_p_1466_ = lean_ctor_get(v_p_1443_, 2);
lean_inc_ref(v_p_1466_);
lean_dec_ref(v_p_1443_);
v___x_1467_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_v_1465_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
if (lean_obj_tag(v_a_1468_) == 1)
{
lean_dec_ref(v_a_1468_);
lean_dec_ref(v_p_1466_);
return v___x_1467_;
}
else
{
lean_dec_ref(v___x_1467_);
lean_dec(v_a_1468_);
v_p_1443_ = v_p_1466_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1466_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1483_;
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
