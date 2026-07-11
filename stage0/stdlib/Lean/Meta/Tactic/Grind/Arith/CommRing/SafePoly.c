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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_38_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_38_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_38_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_38_;
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
lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_37_; 
v_val_25_ = lean_ctor_get(v_charInst_x3f_24_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v_charInst_x3f_24_);
if (v_isSharedCheck_37_ == 0)
{
v___x_27_ = v_charInst_x3f_24_;
v_isShared_28_ = v_isSharedCheck_37_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_dec(v_charInst_x3f_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_37_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_snd_29_; lean_object* v___x_30_; uint8_t v___x_31_; uint8_t v___x_32_; 
v_snd_29_ = lean_ctor_get(v_val_25_, 1);
lean_inc(v_snd_29_);
lean_dec(v_val_25_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v_snd_29_, v___x_30_);
v___x_32_ = lean_bool_not(v___x_31_);
if (v___x_32_ == 0)
{
lean_dec(v_snd_29_);
lean_del_object(v___x_27_);
goto v___jp_18_;
}
else
{
lean_object* v___x_34_; 
lean_del_object(v___x_16_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v_snd_29_);
v___x_34_ = v___x_27_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_snd_29_);
v___x_34_ = v_reuseFailAlloc_36_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
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
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_13_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_13_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0___boxed(lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_nat_to_int(v_a_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_89_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_89_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_89_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_89_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
if (lean_obj_tag(v_a_76_) == 1)
{
lean_object* v_val_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v_val_80_ = lean_ctor_get(v_a_76_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v_a_76_, 1);
v___x_81_ = lean_nat_to_int(v_val_80_);
v___x_82_ = lean_int_emod(v_a_62_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v_a_62_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_82_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_a_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v_a_62_);
v___x_87_ = v___x_78_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_62_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
lean_dec(v_a_62_);
v_a_90_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_75_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_75_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar___boxed(lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(lean_object* v_p_112_, lean_object* v_k_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_140_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_140_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_140_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_140_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
if (lean_obj_tag(v_a_127_) == 1)
{
lean_object* v_val_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v_val_131_ = lean_ctor_get(v_a_127_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v_a_127_, 1);
v___x_132_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_112_, v_k_113_, v_val_131_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_132_);
v___x_134_ = v___x_129_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_138_; 
lean_dec(v_a_127_);
v___x_136_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_112_, v_k_113_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_136_);
v___x_138_ = v___x_129_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v_p_112_);
v_a_141_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_126_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_126_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst___boxed(lean_object* v_p_149_, lean_object* v_k_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_149_, v_k_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_k_150_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(lean_object* v_k_164_, lean_object* v_p_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_192_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_192_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
if (lean_obj_tag(v_a_179_) == 1)
{
lean_object* v_val_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v_val_183_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v_a_179_, 1);
v___x_184_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_164_, v_p_165_, v_val_183_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec(v_a_179_);
v___x_188_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_164_, v_p_165_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_188_);
v___x_190_ = v___x_181_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_p_165_);
v_a_193_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_178_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_178_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst___boxed(lean_object* v_k_201_, lean_object* v_p_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_201_, v_p_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_k_201_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(lean_object* v_k_216_, lean_object* v_m_217_, lean_object* v_p_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_245_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_245_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
if (lean_obj_tag(v_a_232_) == 1)
{
lean_object* v_val_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v_val_236_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v_a_232_, 1);
v___x_237_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_216_, v_m_217_, v_p_218_, v_val_236_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_243_; 
lean_dec(v_a_232_);
v___x_241_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_216_, v_m_217_, v_p_218_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_243_ = v___x_234_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_p_218_);
lean_dec(v_m_217_);
v_a_246_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_231_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_231_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon___boxed(lean_object* v_k_254_, lean_object* v_m_255_, lean_object* v_p_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_254_, v_m_255_, v_p_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_k_254_);
return v_res_269_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = l_Lean_maxRecDepthErrorMessage;
v___x_276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3);
v___x_278_ = l_Lean_MessageData_ofFormat(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4);
v___x_280_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2));
v___x_281_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(lean_object* v_ref_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_ref_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___boxed(lean_object* v_ref_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(lean_object* v_00_u03b1_290_, lean_object* v_ref_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_291_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___boxed(lean_object* v_00_u03b1_305_, lean_object* v_ref_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(v_00_u03b1_305_, v_ref_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
return v_res_319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(lean_object* v_p_u2081_322_, lean_object* v_p_u2082_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_options_338_; lean_object* v_currRecDepth_339_; lean_object* v_maxRecDepth_340_; lean_object* v_ref_341_; lean_object* v_currNamespace_342_; lean_object* v_openDecls_343_; lean_object* v_initHeartbeats_344_; lean_object* v_maxHeartbeats_345_; lean_object* v_quotContext_346_; lean_object* v_currMacroScope_347_; uint8_t v_diag_348_; lean_object* v_cancelTk_x3f_349_; uint8_t v_suppressElabErrors_350_; lean_object* v_inheritedTraceOptions_351_; uint8_t v___y_353_; lean_object* v___x_467_; uint8_t v___x_468_; uint8_t v___x_469_; 
v_fileName_336_ = lean_ctor_get(v_a_333_, 0);
lean_inc_ref(v_fileName_336_);
v_fileMap_337_ = lean_ctor_get(v_a_333_, 1);
lean_inc_ref(v_fileMap_337_);
v_options_338_ = lean_ctor_get(v_a_333_, 2);
lean_inc_ref(v_options_338_);
v_currRecDepth_339_ = lean_ctor_get(v_a_333_, 3);
lean_inc(v_currRecDepth_339_);
v_maxRecDepth_340_ = lean_ctor_get(v_a_333_, 4);
lean_inc(v_maxRecDepth_340_);
v_ref_341_ = lean_ctor_get(v_a_333_, 5);
lean_inc(v_ref_341_);
v_currNamespace_342_ = lean_ctor_get(v_a_333_, 6);
lean_inc(v_currNamespace_342_);
v_openDecls_343_ = lean_ctor_get(v_a_333_, 7);
lean_inc(v_openDecls_343_);
v_initHeartbeats_344_ = lean_ctor_get(v_a_333_, 8);
lean_inc(v_initHeartbeats_344_);
v_maxHeartbeats_345_ = lean_ctor_get(v_a_333_, 9);
lean_inc(v_maxHeartbeats_345_);
v_quotContext_346_ = lean_ctor_get(v_a_333_, 10);
lean_inc(v_quotContext_346_);
v_currMacroScope_347_ = lean_ctor_get(v_a_333_, 11);
lean_inc(v_currMacroScope_347_);
v_diag_348_ = lean_ctor_get_uint8(v_a_333_, sizeof(void*)*14);
v_cancelTk_x3f_349_ = lean_ctor_get(v_a_333_, 12);
lean_inc(v_cancelTk_x3f_349_);
v_suppressElabErrors_350_ = lean_ctor_get_uint8(v_a_333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_351_ = lean_ctor_get(v_a_333_, 13);
lean_inc_ref(v_inheritedTraceOptions_351_);
lean_dec_ref(v_a_333_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_nat_dec_eq(v_maxRecDepth_340_, v___x_467_);
v___x_469_ = lean_bool_not(v___x_468_);
if (v___x_469_ == 0)
{
v___y_353_ = v___x_469_;
goto v___jp_352_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_eq(v_currRecDepth_339_, v_maxRecDepth_340_);
v___y_353_ = v___x_470_;
goto v___jp_352_;
}
v___jp_352_:
{
if (v___y_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_currRecDepth_339_, v___x_354_);
lean_dec(v_currRecDepth_339_);
v___x_356_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_356_, 0, v_fileName_336_);
lean_ctor_set(v___x_356_, 1, v_fileMap_337_);
lean_ctor_set(v___x_356_, 2, v_options_338_);
lean_ctor_set(v___x_356_, 3, v___x_355_);
lean_ctor_set(v___x_356_, 4, v_maxRecDepth_340_);
lean_ctor_set(v___x_356_, 5, v_ref_341_);
lean_ctor_set(v___x_356_, 6, v_currNamespace_342_);
lean_ctor_set(v___x_356_, 7, v_openDecls_343_);
lean_ctor_set(v___x_356_, 8, v_initHeartbeats_344_);
lean_ctor_set(v___x_356_, 9, v_maxHeartbeats_345_);
lean_ctor_set(v___x_356_, 10, v_quotContext_346_);
lean_ctor_set(v___x_356_, 11, v_currMacroScope_347_);
lean_ctor_set(v___x_356_, 12, v_cancelTk_x3f_349_);
lean_ctor_set(v___x_356_, 13, v_inheritedTraceOptions_351_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*14, v_diag_348_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*14 + 1, v_suppressElabErrors_350_);
if (lean_obj_tag(v_p_u2081_322_) == 0)
{
if (lean_obj_tag(v_p_u2082_323_) == 0)
{
lean_object* v_k_357_; lean_object* v_k_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_383_; 
v_k_357_ = lean_ctor_get(v_p_u2081_322_, 0);
lean_inc(v_k_357_);
lean_dec_ref_known(v_p_u2081_322_, 1);
v_k_358_ = lean_ctor_get(v_p_u2082_323_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_p_u2082_323_);
if (v_isSharedCheck_383_ == 0)
{
v___x_360_ = v_p_u2082_323_;
v_isShared_361_ = v_isSharedCheck_383_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_k_358_);
lean_dec(v_p_u2082_323_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_383_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_int_add(v_k_357_, v_k_358_);
lean_dec(v_k_358_);
lean_dec(v_k_357_);
v___x_363_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_362_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
lean_dec_ref_known(v___x_356_, 14);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_374_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_a_364_);
v___x_369_ = v___x_360_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_del_object(v___x_360_);
v_a_375_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_363_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_363_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
else
{
lean_object* v_k_384_; lean_object* v___x_385_; 
v_k_384_ = lean_ctor_get(v_p_u2081_322_, 0);
lean_inc(v_k_384_);
lean_dec_ref_known(v_p_u2081_322_, 1);
v___x_385_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2082_323_, v_k_384_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
lean_dec_ref_known(v___x_356_, 14);
lean_dec(v_k_384_);
return v___x_385_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_323_) == 0)
{
lean_object* v_k_386_; lean_object* v___x_387_; 
v_k_386_ = lean_ctor_get(v_p_u2082_323_, 0);
lean_inc(v_k_386_);
lean_dec_ref_known(v_p_u2082_323_, 1);
v___x_387_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2081_322_, v_k_386_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
lean_dec_ref_known(v___x_356_, 14);
lean_dec(v_k_386_);
return v___x_387_;
}
else
{
lean_object* v_k_388_; lean_object* v_v_389_; lean_object* v_p_390_; lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v_p_393_; uint8_t v___x_394_; 
v_k_388_ = lean_ctor_get(v_p_u2081_322_, 0);
v_v_389_ = lean_ctor_get(v_p_u2081_322_, 1);
v_p_390_ = lean_ctor_get(v_p_u2081_322_, 2);
v_k_391_ = lean_ctor_get(v_p_u2082_323_, 0);
v_v_392_ = lean_ctor_get(v_p_u2082_323_, 1);
v_p_393_ = lean_ctor_get(v_p_u2082_323_, 2);
v___x_394_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_389_, v_v_392_);
switch(v___x_394_)
{
case 0:
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_410_; 
lean_inc_ref(v_p_393_);
lean_inc(v_v_392_);
lean_inc(v_k_391_);
v_isSharedCheck_410_ = !lean_is_exclusive(v_p_u2082_323_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_411_ = lean_ctor_get(v_p_u2082_323_, 2);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_p_u2082_323_, 1);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_p_u2082_323_, 0);
lean_dec(v_unused_413_);
v___x_396_ = v_p_u2082_323_;
v_isShared_397_ = v_isSharedCheck_410_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_p_u2082_323_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_410_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_322_, v_p_393_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 2, v_a_399_);
v___x_404_ = v___x_396_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_k_391_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_v_392_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_a_399_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_del_object(v___x_396_);
lean_dec(v_v_392_);
lean_dec(v_k_391_);
return v___x_398_;
}
}
}
case 1:
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_443_; 
lean_inc_ref(v_p_393_);
lean_inc(v_k_391_);
lean_inc_ref(v_p_390_);
lean_inc(v_v_389_);
lean_inc(v_k_388_);
lean_dec_ref_known(v_p_u2081_322_, 3);
v_isSharedCheck_443_ = !lean_is_exclusive(v_p_u2082_323_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_444_ = lean_ctor_get(v_p_u2082_323_, 2);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_p_u2082_323_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_p_u2082_323_, 0);
lean_dec(v_unused_446_);
v___x_415_ = v_p_u2082_323_;
v_isShared_416_ = v_isSharedCheck_443_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_p_u2082_323_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_443_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_int_add(v_k_388_, v_k_391_);
lean_dec(v_k_391_);
lean_dec(v_k_388_);
v___x_418_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_417_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_421_ = lean_int_dec_eq(v_a_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_390_, v_p_393_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_433_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 2, v_a_423_);
lean_ctor_set(v___x_415_, 1, v_v_389_);
lean_ctor_set(v___x_415_, 0, v_a_419_);
v___x_428_ = v___x_415_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_v_389_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_a_423_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_430_ = v___x_425_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_dec(v_a_419_);
lean_del_object(v___x_415_);
lean_dec(v_v_389_);
return v___x_422_;
}
}
else
{
lean_dec(v_a_419_);
lean_del_object(v___x_415_);
lean_dec(v_v_389_);
v_p_u2081_322_ = v_p_390_;
v_p_u2082_323_ = v_p_393_;
v_a_333_ = v___x_356_;
goto _start;
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_del_object(v___x_415_);
lean_dec_ref(v_p_393_);
lean_dec_ref(v_p_390_);
lean_dec(v_v_389_);
lean_dec_ref_known(v___x_356_, 14);
v_a_435_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_418_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_418_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
default: 
{
lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_462_; 
lean_inc_ref(v_p_390_);
lean_inc(v_v_389_);
lean_inc(v_k_388_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_p_u2081_322_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; 
v_unused_463_ = lean_ctor_get(v_p_u2081_322_, 2);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_p_u2081_322_, 1);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_p_u2081_322_, 0);
lean_dec(v_unused_465_);
v___x_448_ = v_p_u2081_322_;
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
else
{
lean_dec(v_p_u2081_322_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; 
v___x_450_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_390_, v_p_u2082_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v___x_356_, v_a_334_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_461_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_461_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_461_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_461_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v_a_451_);
v___x_456_ = v___x_448_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_k_388_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_v_389_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_a_451_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
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
else
{
lean_del_object(v___x_448_);
lean_dec(v_v_389_);
lean_dec(v_k_388_);
return v___x_450_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v_inheritedTraceOptions_351_);
lean_dec(v_cancelTk_x3f_349_);
lean_dec(v_currMacroScope_347_);
lean_dec(v_quotContext_346_);
lean_dec(v_maxHeartbeats_345_);
lean_dec(v_initHeartbeats_344_);
lean_dec(v_openDecls_343_);
lean_dec(v_currNamespace_342_);
lean_dec(v_maxRecDepth_340_);
lean_dec(v_currRecDepth_339_);
lean_dec_ref(v_options_338_);
lean_dec_ref(v_fileMap_337_);
lean_dec_ref(v_fileName_336_);
lean_dec_ref(v_p_u2082_323_);
lean_dec_ref(v_p_u2081_322_);
v___x_466_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_341_);
return v___x_466_;
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
lean_dec_ref_known(v_p_u2081_486_, 1);
v_k_493_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_493_);
lean_dec_ref_known(v_p_u2082_487_, 1);
v___x_494_ = lean_apply_2(v_h__1_488_, v_k_492_, v_k_493_);
return v___x_494_;
}
else
{
lean_object* v_k_495_; lean_object* v_k_496_; lean_object* v_v_497_; lean_object* v_p_498_; lean_object* v___x_499_; 
lean_dec(v_h__1_488_);
v_k_495_ = lean_ctor_get(v_p_u2081_486_, 0);
lean_inc(v_k_495_);
lean_dec_ref_known(v_p_u2081_486_, 1);
v_k_496_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_496_);
v_v_497_ = lean_ctor_get(v_p_u2082_487_, 1);
lean_inc(v_v_497_);
v_p_498_ = lean_ctor_get(v_p_u2082_487_, 2);
lean_inc_ref(v_p_498_);
lean_dec_ref_known(v_p_u2082_487_, 3);
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
lean_dec_ref_known(v_p_u2081_486_, 3);
v_k_503_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_503_);
lean_dec_ref_known(v_p_u2082_487_, 1);
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
lean_dec_ref_known(v_p_u2081_486_, 3);
v_k_508_ = lean_ctor_get(v_p_u2082_487_, 0);
lean_inc(v_k_508_);
v_v_509_ = lean_ctor_get(v_p_u2082_487_, 1);
lean_inc(v_v_509_);
v_p_510_ = lean_ctor_get(v_p_u2082_487_, 2);
lean_inc_ref(v_p_510_);
lean_dec_ref_known(v_p_u2082_487_, 3);
v___x_511_ = lean_apply_6(v_h__4_491_, v_k_505_, v_v_506_, v_p_507_, v_k_508_, v_v_509_, v_p_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object* v_motive_512_, lean_object* v_p_u2081_513_, lean_object* v_p_u2082_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_, lean_object* v_h__3_517_, lean_object* v_h__4_518_){
_start:
{
if (lean_obj_tag(v_p_u2081_513_) == 0)
{
lean_dec(v_h__4_518_);
lean_dec(v_h__3_517_);
if (lean_obj_tag(v_p_u2082_514_) == 0)
{
lean_object* v_k_519_; lean_object* v_k_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_516_);
v_k_519_ = lean_ctor_get(v_p_u2081_513_, 0);
lean_inc(v_k_519_);
lean_dec_ref_known(v_p_u2081_513_, 1);
v_k_520_ = lean_ctor_get(v_p_u2082_514_, 0);
lean_inc(v_k_520_);
lean_dec_ref_known(v_p_u2082_514_, 1);
v___x_521_ = lean_apply_2(v_h__1_515_, v_k_519_, v_k_520_);
return v___x_521_;
}
else
{
lean_object* v_k_522_; lean_object* v_k_523_; lean_object* v_v_524_; lean_object* v_p_525_; lean_object* v___x_526_; 
lean_dec(v_h__1_515_);
v_k_522_ = lean_ctor_get(v_p_u2081_513_, 0);
lean_inc(v_k_522_);
lean_dec_ref_known(v_p_u2081_513_, 1);
v_k_523_ = lean_ctor_get(v_p_u2082_514_, 0);
lean_inc(v_k_523_);
v_v_524_ = lean_ctor_get(v_p_u2082_514_, 1);
lean_inc(v_v_524_);
v_p_525_ = lean_ctor_get(v_p_u2082_514_, 2);
lean_inc_ref(v_p_525_);
lean_dec_ref_known(v_p_u2082_514_, 3);
v___x_526_ = lean_apply_4(v_h__2_516_, v_k_522_, v_k_523_, v_v_524_, v_p_525_);
return v___x_526_;
}
}
else
{
lean_dec(v_h__2_516_);
lean_dec(v_h__1_515_);
if (lean_obj_tag(v_p_u2082_514_) == 0)
{
lean_object* v_k_527_; lean_object* v_v_528_; lean_object* v_p_529_; lean_object* v_k_530_; lean_object* v___x_531_; 
lean_dec(v_h__4_518_);
v_k_527_ = lean_ctor_get(v_p_u2081_513_, 0);
lean_inc(v_k_527_);
v_v_528_ = lean_ctor_get(v_p_u2081_513_, 1);
lean_inc(v_v_528_);
v_p_529_ = lean_ctor_get(v_p_u2081_513_, 2);
lean_inc_ref(v_p_529_);
lean_dec_ref_known(v_p_u2081_513_, 3);
v_k_530_ = lean_ctor_get(v_p_u2082_514_, 0);
lean_inc(v_k_530_);
lean_dec_ref_known(v_p_u2082_514_, 1);
v___x_531_ = lean_apply_4(v_h__3_517_, v_k_527_, v_v_528_, v_p_529_, v_k_530_);
return v___x_531_;
}
else
{
lean_object* v_k_532_; lean_object* v_v_533_; lean_object* v_p_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_p_537_; lean_object* v___x_538_; 
lean_dec(v_h__3_517_);
v_k_532_ = lean_ctor_get(v_p_u2081_513_, 0);
lean_inc(v_k_532_);
v_v_533_ = lean_ctor_get(v_p_u2081_513_, 1);
lean_inc(v_v_533_);
v_p_534_ = lean_ctor_get(v_p_u2081_513_, 2);
lean_inc_ref(v_p_534_);
lean_dec_ref_known(v_p_u2081_513_, 3);
v_k_535_ = lean_ctor_get(v_p_u2082_514_, 0);
lean_inc(v_k_535_);
v_v_536_ = lean_ctor_get(v_p_u2082_514_, 1);
lean_inc(v_v_536_);
v_p_537_ = lean_ctor_get(v_p_u2082_514_, 2);
lean_inc_ref(v_p_537_);
lean_dec_ref_known(v_p_u2082_514_, 3);
v___x_538_ = lean_apply_6(v_h__4_518_, v_k_532_, v_v_533_, v_p_534_, v_k_535_, v_v_536_, v_p_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t v_x_539_, lean_object* v_h__1_540_, lean_object* v_h__2_541_, lean_object* v_h__3_542_){
_start:
{
switch(v_x_539_)
{
case 0:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_h__2_541_);
lean_dec(v_h__1_540_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_1(v_h__3_542_, v___x_543_);
return v___x_544_;
}
case 1:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_h__3_542_);
lean_dec(v_h__2_541_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_apply_1(v_h__1_540_, v___x_545_);
return v___x_546_;
}
default: 
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_h__3_542_);
lean_dec(v_h__1_540_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_apply_1(v_h__2_541_, v___x_547_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object* v_x_549_, lean_object* v_h__1_550_, lean_object* v_h__2_551_, lean_object* v_h__3_552_){
_start:
{
uint8_t v_x_33__boxed_553_; lean_object* v_res_554_; 
v_x_33__boxed_553_ = lean_unbox(v_x_549_);
v_res_554_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_33__boxed_553_, v_h__1_550_, v_h__2_551_, v_h__3_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object* v_motive_555_, uint8_t v_x_556_, lean_object* v_h__1_557_, lean_object* v_h__2_558_, lean_object* v_h__3_559_){
_start:
{
switch(v_x_556_)
{
case 0:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_h__2_558_);
lean_dec(v_h__1_557_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_1(v_h__3_559_, v___x_560_);
return v___x_561_;
}
case 1:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_h__3_559_);
lean_dec(v_h__2_558_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_apply_1(v_h__1_557_, v___x_562_);
return v___x_563_;
}
default: 
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_h__3_559_);
lean_dec(v_h__1_557_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_apply_1(v_h__2_558_, v___x_564_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object* v_motive_566_, lean_object* v_x_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_, lean_object* v_h__3_570_){
_start:
{
uint8_t v_x_48__boxed_571_; lean_object* v_res_572_; 
v_x_48__boxed_571_ = lean_unbox(v_x_567_);
v_res_572_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_566_, v_x_48__boxed_571_, v_h__1_568_, v_h__2_569_, v_h__3_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object* v_p_u2082_574_, lean_object* v_p_u2081_575_, lean_object* v_acc_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_fileName_589_; lean_object* v_fileMap_590_; lean_object* v_options_591_; lean_object* v_currRecDepth_592_; lean_object* v_maxRecDepth_593_; lean_object* v_ref_594_; lean_object* v_currNamespace_595_; lean_object* v_openDecls_596_; lean_object* v_initHeartbeats_597_; lean_object* v_maxHeartbeats_598_; lean_object* v_quotContext_599_; lean_object* v_currMacroScope_600_; uint8_t v_diag_601_; lean_object* v_cancelTk_x3f_602_; uint8_t v_suppressElabErrors_603_; lean_object* v_inheritedTraceOptions_604_; uint8_t v___y_606_; lean_object* v___x_633_; uint8_t v___x_634_; uint8_t v___x_635_; 
v_fileName_589_ = lean_ctor_get(v_a_586_, 0);
lean_inc_ref(v_fileName_589_);
v_fileMap_590_ = lean_ctor_get(v_a_586_, 1);
lean_inc_ref(v_fileMap_590_);
v_options_591_ = lean_ctor_get(v_a_586_, 2);
lean_inc_ref(v_options_591_);
v_currRecDepth_592_ = lean_ctor_get(v_a_586_, 3);
lean_inc(v_currRecDepth_592_);
v_maxRecDepth_593_ = lean_ctor_get(v_a_586_, 4);
lean_inc(v_maxRecDepth_593_);
v_ref_594_ = lean_ctor_get(v_a_586_, 5);
lean_inc(v_ref_594_);
v_currNamespace_595_ = lean_ctor_get(v_a_586_, 6);
lean_inc(v_currNamespace_595_);
v_openDecls_596_ = lean_ctor_get(v_a_586_, 7);
lean_inc(v_openDecls_596_);
v_initHeartbeats_597_ = lean_ctor_get(v_a_586_, 8);
lean_inc(v_initHeartbeats_597_);
v_maxHeartbeats_598_ = lean_ctor_get(v_a_586_, 9);
lean_inc(v_maxHeartbeats_598_);
v_quotContext_599_ = lean_ctor_get(v_a_586_, 10);
lean_inc(v_quotContext_599_);
v_currMacroScope_600_ = lean_ctor_get(v_a_586_, 11);
lean_inc(v_currMacroScope_600_);
v_diag_601_ = lean_ctor_get_uint8(v_a_586_, sizeof(void*)*14);
v_cancelTk_x3f_602_ = lean_ctor_get(v_a_586_, 12);
lean_inc(v_cancelTk_x3f_602_);
v_suppressElabErrors_603_ = lean_ctor_get_uint8(v_a_586_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_604_ = lean_ctor_get(v_a_586_, 13);
lean_inc_ref(v_inheritedTraceOptions_604_);
lean_dec_ref(v_a_586_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_nat_dec_eq(v_maxRecDepth_593_, v___x_633_);
v___x_635_ = lean_bool_not(v___x_634_);
if (v___x_635_ == 0)
{
v___y_606_ = v___x_635_;
goto v___jp_605_;
}
else
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_eq(v_currRecDepth_592_, v_maxRecDepth_593_);
v___y_606_ = v___x_636_;
goto v___jp_605_;
}
v___jp_605_:
{
if (v___y_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_currRecDepth_592_, v___x_607_);
lean_dec(v_currRecDepth_592_);
v___x_609_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_609_, 0, v_fileName_589_);
lean_ctor_set(v___x_609_, 1, v_fileMap_590_);
lean_ctor_set(v___x_609_, 2, v_options_591_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
lean_ctor_set(v___x_609_, 4, v_maxRecDepth_593_);
lean_ctor_set(v___x_609_, 5, v_ref_594_);
lean_ctor_set(v___x_609_, 6, v_currNamespace_595_);
lean_ctor_set(v___x_609_, 7, v_openDecls_596_);
lean_ctor_set(v___x_609_, 8, v_initHeartbeats_597_);
lean_ctor_set(v___x_609_, 9, v_maxHeartbeats_598_);
lean_ctor_set(v___x_609_, 10, v_quotContext_599_);
lean_ctor_set(v___x_609_, 11, v_currMacroScope_600_);
lean_ctor_set(v___x_609_, 12, v_cancelTk_x3f_602_);
lean_ctor_set(v___x_609_, 13, v_inheritedTraceOptions_604_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*14, v_diag_601_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*14 + 1, v_suppressElabErrors_603_);
if (lean_obj_tag(v_p_u2081_575_) == 0)
{
lean_object* v_k_610_; lean_object* v___x_611_; 
v_k_610_ = lean_ctor_get(v_p_u2081_575_, 0);
lean_inc(v_k_610_);
lean_dec_ref_known(v_p_u2081_575_, 1);
v___x_611_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_610_, v_p_u2082_574_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v___x_609_, v_a_587_);
lean_dec(v_k_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v___x_613_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_576_, v_a_612_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v___x_609_, v_a_587_);
return v___x_613_;
}
else
{
lean_dec_ref_known(v___x_609_, 14);
lean_dec_ref(v_acc_576_);
return v___x_611_;
}
}
else
{
lean_object* v_k_614_; lean_object* v_v_615_; lean_object* v_p_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_k_614_ = lean_ctor_get(v_p_u2081_575_, 0);
lean_inc(v_k_614_);
v_v_615_ = lean_ctor_get(v_p_u2081_575_, 1);
lean_inc(v_v_615_);
v_p_616_ = lean_ctor_get(v_p_u2081_575_, 2);
lean_inc_ref(v_p_616_);
lean_dec_ref_known(v_p_u2081_575_, 3);
v___x_617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
v___x_618_ = l_Lean_Core_checkSystem(v___x_617_, v___x_609_, v_a_587_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_619_; 
lean_dec_ref_known(v___x_618_, 1);
lean_inc_ref(v_p_u2082_574_);
v___x_619_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_614_, v_v_615_, v_p_u2082_574_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v___x_609_, v_a_587_);
lean_dec(v_k_614_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
lean_inc_ref(v___x_609_);
v___x_621_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_576_, v_a_620_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v___x_609_, v_a_587_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v_p_u2081_575_ = v_p_616_;
v_acc_576_ = v_a_622_;
v_a_586_ = v___x_609_;
goto _start;
}
else
{
lean_dec_ref(v_p_616_);
lean_dec_ref_known(v___x_609_, 14);
lean_dec_ref(v_p_u2082_574_);
return v___x_621_;
}
}
else
{
lean_dec_ref(v_p_616_);
lean_dec_ref_known(v___x_609_, 14);
lean_dec_ref(v_acc_576_);
lean_dec_ref(v_p_u2082_574_);
return v___x_619_;
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_p_616_);
lean_dec(v_v_615_);
lean_dec(v_k_614_);
lean_dec_ref_known(v___x_609_, 14);
lean_dec_ref(v_acc_576_);
lean_dec_ref(v_p_u2082_574_);
v_a_624_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_618_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_618_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v___x_632_; 
lean_dec_ref(v_inheritedTraceOptions_604_);
lean_dec(v_cancelTk_x3f_602_);
lean_dec(v_currMacroScope_600_);
lean_dec(v_quotContext_599_);
lean_dec(v_maxHeartbeats_598_);
lean_dec(v_initHeartbeats_597_);
lean_dec(v_openDecls_596_);
lean_dec(v_currNamespace_595_);
lean_dec(v_maxRecDepth_593_);
lean_dec(v_currRecDepth_592_);
lean_dec_ref(v_options_591_);
lean_dec_ref(v_fileMap_590_);
lean_dec_ref(v_fileName_589_);
lean_dec_ref(v_acc_576_);
lean_dec_ref(v_p_u2081_575_);
lean_dec_ref(v_p_u2082_574_);
v___x_632_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_594_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object* v_p_u2082_637_, lean_object* v_p_u2081_638_, lean_object* v_acc_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_637_, v_p_u2081_638_, v_acc_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object* v_p_u2081_655_, lean_object* v_p_u2082_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
lean_inc_ref(v_a_666_);
v___x_670_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_656_, v_p_u2081_655_, v___x_669_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object* v_p_u2081_671_, lean_object* v_p_u2082_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_671_, v_p_u2082_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_to_int(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object* v_p_690_, lean_object* v_k_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_fileName_704_; lean_object* v_fileMap_705_; lean_object* v_options_706_; lean_object* v_currRecDepth_707_; lean_object* v_maxRecDepth_708_; lean_object* v_ref_709_; lean_object* v_currNamespace_710_; lean_object* v_openDecls_711_; lean_object* v_initHeartbeats_712_; lean_object* v_maxHeartbeats_713_; lean_object* v_quotContext_714_; lean_object* v_currMacroScope_715_; uint8_t v_diag_716_; lean_object* v_cancelTk_x3f_717_; uint8_t v_suppressElabErrors_718_; lean_object* v_inheritedTraceOptions_719_; uint8_t v___y_721_; lean_object* v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; 
v_fileName_704_ = lean_ctor_get(v_a_701_, 0);
v_fileMap_705_ = lean_ctor_get(v_a_701_, 1);
v_options_706_ = lean_ctor_get(v_a_701_, 2);
v_currRecDepth_707_ = lean_ctor_get(v_a_701_, 3);
v_maxRecDepth_708_ = lean_ctor_get(v_a_701_, 4);
v_ref_709_ = lean_ctor_get(v_a_701_, 5);
v_currNamespace_710_ = lean_ctor_get(v_a_701_, 6);
v_openDecls_711_ = lean_ctor_get(v_a_701_, 7);
v_initHeartbeats_712_ = lean_ctor_get(v_a_701_, 8);
v_maxHeartbeats_713_ = lean_ctor_get(v_a_701_, 9);
v_quotContext_714_ = lean_ctor_get(v_a_701_, 10);
v_currMacroScope_715_ = lean_ctor_get(v_a_701_, 11);
v_diag_716_ = lean_ctor_get_uint8(v_a_701_, sizeof(void*)*14);
v_cancelTk_x3f_717_ = lean_ctor_get(v_a_701_, 12);
v_suppressElabErrors_718_ = lean_ctor_get_uint8(v_a_701_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_719_ = lean_ctor_get(v_a_701_, 13);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_nat_dec_eq(v_maxRecDepth_708_, v___x_742_);
v___x_744_ = lean_bool_not(v___x_743_);
if (v___x_744_ == 0)
{
v___y_721_ = v___x_744_;
goto v___jp_720_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_eq(v_currRecDepth_707_, v_maxRecDepth_708_);
v___y_721_ = v___x_745_;
goto v___jp_720_;
}
v___jp_720_:
{
if (v___y_721_ == 0)
{
lean_object* v_zero_722_; uint8_t v_isZero_723_; 
v_zero_722_ = lean_unsigned_to_nat(0u);
v_isZero_723_ = lean_nat_dec_eq(v_k_691_, v_zero_722_);
if (v_isZero_723_ == 1)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v_p_690_);
v___x_724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v_one_726_; lean_object* v_n_727_; uint8_t v_isZero_728_; 
v_one_726_ = lean_unsigned_to_nat(1u);
v_n_727_ = lean_nat_sub(v_k_691_, v_one_726_);
v_isZero_728_ = lean_nat_dec_eq(v_n_727_, v_zero_722_);
if (v_isZero_728_ == 1)
{
lean_object* v___x_729_; 
lean_dec(v_n_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_p_690_);
return v___x_729_;
}
else
{
lean_object* v_n_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v_isZero_733_; 
v_n_730_ = lean_nat_sub(v_n_727_, v_one_726_);
lean_dec(v_n_727_);
v___x_731_ = lean_nat_add(v_currRecDepth_707_, v_one_726_);
lean_inc_ref(v_inheritedTraceOptions_719_);
lean_inc(v_cancelTk_x3f_717_);
lean_inc(v_currMacroScope_715_);
lean_inc(v_quotContext_714_);
lean_inc(v_maxHeartbeats_713_);
lean_inc(v_initHeartbeats_712_);
lean_inc(v_openDecls_711_);
lean_inc(v_currNamespace_710_);
lean_inc(v_ref_709_);
lean_inc(v_maxRecDepth_708_);
lean_inc_ref(v_options_706_);
lean_inc_ref(v_fileMap_705_);
lean_inc_ref(v_fileName_704_);
v___x_732_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_732_, 0, v_fileName_704_);
lean_ctor_set(v___x_732_, 1, v_fileMap_705_);
lean_ctor_set(v___x_732_, 2, v_options_706_);
lean_ctor_set(v___x_732_, 3, v___x_731_);
lean_ctor_set(v___x_732_, 4, v_maxRecDepth_708_);
lean_ctor_set(v___x_732_, 5, v_ref_709_);
lean_ctor_set(v___x_732_, 6, v_currNamespace_710_);
lean_ctor_set(v___x_732_, 7, v_openDecls_711_);
lean_ctor_set(v___x_732_, 8, v_initHeartbeats_712_);
lean_ctor_set(v___x_732_, 9, v_maxHeartbeats_713_);
lean_ctor_set(v___x_732_, 10, v_quotContext_714_);
lean_ctor_set(v___x_732_, 11, v_currMacroScope_715_);
lean_ctor_set(v___x_732_, 12, v_cancelTk_x3f_717_);
lean_ctor_set(v___x_732_, 13, v_inheritedTraceOptions_719_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*14, v_diag_716_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*14 + 1, v_suppressElabErrors_718_);
v_isZero_733_ = lean_nat_dec_eq(v_n_730_, v_zero_722_);
if (v_isZero_733_ == 1)
{
lean_object* v___x_734_; 
lean_dec(v_n_730_);
lean_inc_ref(v_p_690_);
v___x_734_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_690_, v_p_690_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v___x_732_, v_a_702_);
lean_dec_ref_known(v___x_732_, 14);
return v___x_734_;
}
else
{
lean_object* v_n_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_n_735_ = lean_nat_sub(v_n_730_, v_one_726_);
lean_dec(v_n_730_);
v___x_736_ = lean_unsigned_to_nat(2u);
v___x_737_ = lean_nat_add(v_n_735_, v___x_736_);
lean_dec(v_n_735_);
lean_inc_ref(v_p_690_);
v___x_738_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_690_, v___x_737_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v___x_732_, v_a_702_);
lean_dec(v___x_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_690_, v_a_739_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v___x_732_, v_a_702_);
lean_dec_ref_known(v___x_732_, 14);
return v___x_740_;
}
else
{
lean_dec_ref_known(v___x_732_, 14);
lean_dec_ref(v_p_690_);
return v___x_738_;
}
}
}
}
}
else
{
lean_object* v___x_741_; 
lean_dec_ref(v_p_690_);
lean_inc(v_ref_709_);
v___x_741_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_709_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object* v_p_746_, lean_object* v_k_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_746_, v_k_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_k_747_);
return v_res_760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
v___x_762_ = lean_int_neg(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object* v_e_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_n_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; 
switch(lean_obj_tag(v_e_765_))
{
case 1:
{
lean_object* v_k_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_836_; 
v_k_810_ = lean_ctor_get(v_e_765_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_e_765_);
if (v_isSharedCheck_836_ == 0)
{
v___x_812_ = v_e_765_;
v_isShared_813_ = v_isSharedCheck_836_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_k_810_);
lean_dec(v_e_765_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_836_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_nat_to_int(v_k_810_);
v___x_815_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_814_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_827_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_827_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_827_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_827_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 0);
lean_ctor_set(v___x_812_, 0, v_a_816_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_826_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_812_);
v_a_828_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_815_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_815_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
case 3:
{
lean_object* v_i_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_846_; 
v_i_837_ = lean_ctor_get(v_e_765_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_e_765_);
if (v_isSharedCheck_846_ == 0)
{
v___x_839_ = v_e_765_;
v_isShared_840_ = v_isSharedCheck_846_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_i_837_);
lean_dec(v_e_765_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_846_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_837_);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
}
case 4:
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_847_);
lean_dec_ref_known(v_e_765_, 1);
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_847_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
if (lean_obj_tag(v_a_849_) == 0)
{
return v___x_848_;
}
else
{
lean_object* v_val_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref_known(v___x_848_, 1);
v_val_850_ = lean_ctor_get(v_a_849_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_a_849_);
if (v_isSharedCheck_875_ == 0)
{
v___x_852_ = v_a_849_;
v_isShared_853_ = v_isSharedCheck_875_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_val_850_);
lean_dec(v_a_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_875_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_855_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_854_, v_val_850_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_a_856_);
v___x_861_ = v___x_852_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_del_object(v___x_852_);
v_a_867_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_855_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_855_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
else
{
return v___x_848_;
}
}
case 5:
{
lean_object* v_a_876_; lean_object* v_b_877_; lean_object* v___x_878_; 
v_a_876_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_876_);
v_b_877_ = lean_ctor_get(v_e_765_, 1);
lean_inc_ref(v_b_877_);
lean_dec_ref_known(v_e_765_, 2);
v___x_878_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_876_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
if (lean_obj_tag(v_a_879_) == 0)
{
lean_dec_ref(v_b_877_);
return v___x_878_;
}
else
{
lean_object* v_val_880_; lean_object* v___x_881_; 
lean_dec_ref_known(v___x_878_, 1);
v_val_880_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_a_879_, 1);
v___x_881_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_877_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
if (lean_obj_tag(v_a_882_) == 0)
{
lean_dec(v_val_880_);
return v___x_881_;
}
else
{
lean_object* v_val_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref_known(v___x_881_, 1);
v_val_883_ = lean_ctor_get(v_a_882_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_907_ == 0)
{
v___x_885_ = v_a_882_;
v_isShared_886_ = v_isSharedCheck_907_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_val_883_);
lean_dec(v_a_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_907_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; 
lean_inc_ref(v_a_775_);
v___x_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_880_, v_val_883_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_898_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_898_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_898_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_898_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_a_888_);
v___x_893_ = v___x_885_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_885_);
v_a_899_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_887_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_887_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
else
{
lean_dec(v_val_880_);
return v___x_881_;
}
}
}
else
{
lean_dec_ref(v_b_877_);
return v___x_878_;
}
}
case 6:
{
lean_object* v_a_908_; lean_object* v_b_909_; lean_object* v___x_910_; 
v_a_908_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_908_);
v_b_909_ = lean_ctor_get(v_e_765_, 1);
lean_inc_ref(v_b_909_);
lean_dec_ref_known(v_e_765_, 2);
v___x_910_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_908_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
if (lean_obj_tag(v_a_911_) == 0)
{
lean_dec_ref(v_b_909_);
return v___x_910_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_913_; 
lean_dec_ref_known(v___x_910_, 1);
v_val_912_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_a_911_, 1);
v___x_913_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_909_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
if (lean_obj_tag(v_a_914_) == 0)
{
lean_dec(v_val_912_);
return v___x_913_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref_known(v___x_913_, 1);
v_val_915_ = lean_ctor_get(v_a_914_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_950_ == 0)
{
v___x_917_ = v_a_914_;
v_isShared_918_ = v_isSharedCheck_950_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_val_915_);
lean_dec(v_a_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_950_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
v___x_920_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_919_, v_val_915_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
lean_inc_ref(v_a_775_);
v___x_922_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_912_, v_a_921_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_933_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_933_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_933_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_933_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_a_923_);
v___x_928_ = v___x_917_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_del_object(v___x_917_);
v_a_934_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_922_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_922_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_del_object(v___x_917_);
lean_dec(v_val_912_);
v_a_942_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_920_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_920_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
else
{
lean_dec(v_val_912_);
return v___x_913_;
}
}
}
else
{
lean_dec_ref(v_b_909_);
return v___x_910_;
}
}
case 7:
{
lean_object* v_a_951_; lean_object* v_b_952_; lean_object* v___x_953_; 
v_a_951_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_951_);
v_b_952_ = lean_ctor_get(v_e_765_, 1);
lean_inc_ref(v_b_952_);
lean_dec_ref_known(v_e_765_, 2);
v___x_953_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_951_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
if (lean_obj_tag(v_a_954_) == 0)
{
lean_dec_ref(v_b_952_);
return v___x_953_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_956_; 
lean_dec_ref_known(v___x_953_, 1);
v_val_955_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v_a_954_, 1);
v___x_956_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_952_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
if (lean_obj_tag(v_a_957_) == 0)
{
lean_dec(v_val_955_);
return v___x_956_;
}
else
{
lean_object* v_val_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref_known(v___x_956_, 1);
v_val_958_ = lean_ctor_get(v_a_957_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_982_ == 0)
{
v___x_960_ = v_a_957_;
v_isShared_961_ = v_isSharedCheck_982_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_val_958_);
lean_dec(v_a_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_982_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_val_955_, v_val_958_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_973_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_973_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v_a_963_);
v___x_968_ = v___x_960_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
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
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_del_object(v___x_960_);
v_a_974_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_962_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_962_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
else
{
lean_dec(v_val_955_);
return v___x_956_;
}
}
}
else
{
lean_dec_ref(v_b_952_);
return v___x_953_;
}
}
case 8:
{
lean_object* v_a_983_; lean_object* v_k_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1080_; 
v_a_983_ = lean_ctor_get(v_e_765_, 0);
v_k_984_ = lean_ctor_get(v_e_765_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_e_765_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_986_ = v_e_765_;
v_isShared_987_ = v_isSharedCheck_1080_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_k_984_);
lean_inc(v_a_983_);
lean_dec(v_e_765_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1080_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_nat_dec_eq(v_k_984_, v___x_988_);
if (v___x_989_ == 0)
{
switch(lean_obj_tag(v_a_983_))
{
case 0:
{
lean_object* v_k_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1035_; 
lean_del_object(v___x_986_);
v_k_990_ = lean_ctor_get(v_a_983_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_992_ = v_a_983_;
v_isShared_993_ = v_isSharedCheck_1035_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_k_990_);
lean_dec(v_a_983_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1035_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; 
lean_inc(v_k_984_);
v___x_994_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_k_984_, v_a_769_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1026_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1026_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1026_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
if (lean_obj_tag(v_a_995_) == 0)
{
if (v___x_989_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_del_object(v___x_992_);
lean_dec(v_k_990_);
lean_dec(v_k_984_);
v___x_1022_ = lean_box(0);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1022_);
v___x_1024_ = v___x_997_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
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
lean_del_object(v___x_997_);
goto v___jp_999_;
}
}
else
{
lean_dec_ref_known(v_a_995_, 1);
lean_del_object(v___x_997_);
goto v___jp_999_;
}
v___jp_999_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l_Int_pow(v_k_990_, v_k_984_);
lean_dec(v_k_984_);
lean_dec(v_k_990_);
v___x_1001_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_1000_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1013_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1013_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1013_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_a_1002_);
v___x_1007_ = v___x_992_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1008_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
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
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_del_object(v___x_992_);
v_a_1014_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1001_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1001_);
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
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_del_object(v___x_992_);
lean_dec(v_k_990_);
lean_dec(v_k_984_);
v_a_1027_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_994_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_994_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1050_; 
v_i_1036_ = lean_ctor_get(v_a_983_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1038_ = v_a_983_;
v_isShared_1039_ = v_isSharedCheck_1050_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_i_1036_);
lean_dec(v_a_983_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1050_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 0, v_i_1036_);
v___x_1041_ = v___x_986_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_i_1036_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_984_);
v___x_1041_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_1043_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1044_);
v___x_1046_ = v___x_1038_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
}
default: 
{
lean_object* v___x_1051_; 
lean_del_object(v___x_986_);
v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_983_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
if (lean_obj_tag(v_a_1052_) == 0)
{
lean_dec(v_k_984_);
return v___x_1051_;
}
else
{
lean_object* v_val_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref_known(v___x_1051_, 1);
v_val_1053_ = lean_ctor_get(v_a_1052_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_a_1052_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1055_ = v_a_1052_;
v_isShared_1056_ = v_isSharedCheck_1077_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_val_1053_);
lean_dec(v_a_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1077_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; 
v___x_1057_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_1053_, v_k_984_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_k_984_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1068_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1058_);
v___x_1063_ = v___x_1055_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1063_);
v___x_1065_ = v___x_1060_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_del_object(v___x_1055_);
v_a_1069_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1057_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1057_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
else
{
lean_dec(v_k_984_);
return v___x_1051_;
}
}
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_del_object(v___x_986_);
lean_dec(v_k_984_);
lean_dec_ref(v_a_983_);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
default: 
{
lean_object* v_k_1081_; 
v_k_1081_ = lean_ctor_get(v_e_765_, 0);
lean_inc(v_k_1081_);
lean_dec_ref(v_e_765_);
v_n_779_ = v_k_1081_;
v___y_780_ = v_a_766_;
v___y_781_ = v_a_767_;
v___y_782_ = v_a_768_;
v___y_783_ = v_a_769_;
v___y_784_ = v_a_770_;
v___y_785_ = v_a_771_;
v___y_786_ = v_a_772_;
v___y_787_ = v_a_773_;
v___y_788_ = v_a_774_;
v___y_789_ = v_a_775_;
v___y_790_ = v_a_776_;
goto v___jp_778_;
}
}
v___jp_778_:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_n_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_801_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_801_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_801_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_801_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_a_792_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_797_);
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_802_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_791_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_791_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object* v_e_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* v_e_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* v_e_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_e_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* v_p_1124_, lean_object* v_k_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1125_, v_p_1124_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* v_p_1139_, lean_object* v_k_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Grind_CommRing_Poly_mulConstM(v_p_1139_, v_k_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_k_1140_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* v_p_1154_, lean_object* v_k_1155_, lean_object* v_m_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1155_, v_m_1156_, v_p_1154_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* v_p_1170_, lean_object* v_k_1171_, lean_object* v_m_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Grind_CommRing_Poly_mulMonM(v_p_1170_, v_k_1171_, v_m_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_k_1171_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* v_p_u2081_1186_, lean_object* v_p_u2082_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_1186_, v_p_u2082_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* v_p_u2081_1201_, lean_object* v_p_u2082_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Grind_CommRing_Poly_mulM(v_p_u2081_1201_, v_p_u2082_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* v_p_u2081_1216_, lean_object* v_p_u2082_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; 
lean_inc_ref(v_a_1227_);
v___x_1230_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_1216_, v_p_u2082_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* v_p_u2081_1231_, lean_object* v_p_u2082_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Grind_CommRing_Poly_combineM(v_p_u2081_1231_, v_p_u2082_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1245_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
v___x_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1246_);
lean_ctor_set(v___x_1249_, 3, v___x_1247_);
lean_ctor_set(v___x_1249_, 4, v___x_1246_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* v_p_u2081_1250_, lean_object* v_p_u2082_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
if (lean_obj_tag(v_p_u2081_1250_) == 1)
{
if (lean_obj_tag(v_p_u2082_1251_) == 1)
{
lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_p_1269_; lean_object* v_k_1270_; lean_object* v_v_1271_; lean_object* v_p_1272_; lean_object* v_m_1273_; lean_object* v_m_u2081_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_g_1277_; lean_object* v___x_1278_; lean_object* v_c_u2081_1279_; lean_object* v___x_1280_; 
v_k_1267_ = lean_ctor_get(v_p_u2081_1250_, 0);
lean_inc(v_k_1267_);
v_v_1268_ = lean_ctor_get(v_p_u2081_1250_, 1);
lean_inc_n(v_v_1268_, 2);
v_p_1269_ = lean_ctor_get(v_p_u2081_1250_, 2);
lean_inc_ref(v_p_1269_);
lean_dec_ref_known(v_p_u2081_1250_, 3);
v_k_1270_ = lean_ctor_get(v_p_u2082_1251_, 0);
lean_inc(v_k_1270_);
v_v_1271_ = lean_ctor_get(v_p_u2082_1251_, 1);
lean_inc_n(v_v_1271_, 2);
v_p_1272_ = lean_ctor_get(v_p_u2082_1251_, 2);
lean_inc_ref(v_p_1272_);
lean_dec_ref_known(v_p_u2082_1251_, 3);
v_m_1273_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_1268_, v_v_1271_);
lean_inc(v_m_1273_);
v_m_u2081_1274_ = l_Lean_Grind_CommRing_Mon_div(v_m_1273_, v_v_1268_);
v___x_1275_ = lean_nat_abs(v_k_1267_);
v___x_1276_ = lean_nat_abs(v_k_1270_);
v_g_1277_ = lean_nat_gcd(v___x_1275_, v___x_1276_);
lean_dec(v___x_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_nat_to_int(v_g_1277_);
v_c_u2081_1279_ = lean_int_ediv(v_k_1270_, v___x_1278_);
lean_dec(v_k_1270_);
lean_inc(v_m_u2081_1274_);
v___x_1280_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_1279_, v_m_u2081_1274_, v_p_1269_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_m_u2082_1282_; lean_object* v___x_1283_; lean_object* v_c_u2082_1284_; lean_object* v___x_1285_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v_m_u2082_1282_ = l_Lean_Grind_CommRing_Mon_div(v_m_1273_, v_v_1271_);
v___x_1283_ = lean_int_neg(v_k_1267_);
lean_dec(v_k_1267_);
v_c_u2082_1284_ = lean_int_ediv(v___x_1283_, v___x_1278_);
lean_dec(v___x_1278_);
lean_dec(v___x_1283_);
lean_inc(v_m_u2082_1282_);
v___x_1285_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_1284_, v_m_u2082_1282_, v_p_1272_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
lean_inc_ref(v_a_1261_);
v___x_1287_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1281_, v_a_1286_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1296_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1292_, 0, v_a_1288_);
lean_ctor_set(v___x_1292_, 1, v_c_u2081_1279_);
lean_ctor_set(v___x_1292_, 2, v_m_u2081_1274_);
lean_ctor_set(v___x_1292_, 3, v_c_u2082_1284_);
lean_ctor_set(v___x_1292_, 4, v_m_u2082_1282_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_c_u2082_1284_);
lean_dec(v_m_u2082_1282_);
lean_dec(v_c_u2081_1279_);
lean_dec(v_m_u2081_1274_);
v_a_1297_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1287_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1287_);
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
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_c_u2082_1284_);
lean_dec(v_m_u2082_1282_);
lean_dec(v_a_1281_);
lean_dec(v_c_u2081_1279_);
lean_dec(v_m_u2081_1274_);
v_a_1305_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1285_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1285_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_c_u2081_1279_);
lean_dec(v___x_1278_);
lean_dec(v_m_u2081_1274_);
lean_dec(v_m_1273_);
lean_dec_ref(v_p_1272_);
lean_dec(v_v_1271_);
lean_dec(v_k_1267_);
v_a_1313_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1280_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1280_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_dec_ref_known(v_p_u2081_1250_, 3);
lean_dec_ref(v_p_u2082_1251_);
goto v___jp_1264_;
}
}
else
{
lean_dec_ref(v_p_u2082_1251_);
lean_dec_ref(v_p_u2081_1250_);
goto v___jp_1264_;
}
v___jp_1264_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* v_p_u2081_1321_, lean_object* v_p_u2082_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Grind_CommRing_Poly_spolM(v_p_u2081_1321_, v_p_u2082_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* v_m_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
if (lean_obj_tag(v_m_1346_) == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v_p_1361_; lean_object* v_m_1362_; lean_object* v___x_1363_; 
v_p_1361_ = lean_ctor_get(v_m_1346_, 0);
lean_inc_ref(v_p_1361_);
v_m_1362_ = lean_ctor_get(v_m_1346_, 1);
lean_inc(v_m_1362_);
lean_dec_ref_known(v_m_1346_, 2);
v___x_1363_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_toRing_1365_; lean_object* v_vars_1366_; lean_object* v_x_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1435_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v_toRing_1365_ = lean_ctor_get(v_a_1364_, 0);
lean_inc_ref(v_toRing_1365_);
lean_dec(v_a_1364_);
v_vars_1366_ = lean_ctor_get(v_toRing_1365_, 14);
lean_inc_ref(v_vars_1366_);
lean_dec_ref(v_toRing_1365_);
v_x_1367_ = lean_ctor_get(v_p_1361_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_p_1361_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_p_1361_, 1);
lean_dec(v_unused_1436_);
v___x_1369_ = v_p_1361_;
v_isShared_1370_ = v_isSharedCheck_1435_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_x_1367_);
lean_dec(v_p_1361_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1435_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___y_1372_; lean_object* v_size_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v_size_1430_ = lean_ctor_get(v_vars_1366_, 2);
v___x_1431_ = l_Lean_instInhabitedExpr;
v___x_1432_ = lean_nat_dec_lt(v_x_1367_, v_size_1430_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref(v_vars_1366_);
v___x_1433_ = l_outOfBounds___redArg(v___x_1431_);
v___y_1372_ = v___x_1433_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1431_, v_vars_1366_, v_x_1367_);
lean_dec_ref(v_vars_1366_);
v___y_1372_ = v___x_1434_;
goto v___jp_1371_;
}
v___jp_1371_:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = l_Lean_Expr_cleanupAnnotations(v___y_1372_);
v___x_1374_ = l_Lean_Expr_isApp(v___x_1373_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v_arg_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_arg_1376_ = lean_ctor_get(v___x_1373_, 1);
lean_inc_ref(v_arg_1376_);
v___x_1377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1373_);
v___x_1378_ = l_Lean_Expr_isApp(v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v___x_1377_);
lean_dec_ref(v_arg_1376_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1377_);
v___x_1381_ = l_Lean_Expr_isApp(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v___x_1380_);
lean_dec_ref(v_arg_1376_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1380_);
v___x_1384_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
v___x_1385_ = l_Lean_Expr_isConstOf(v___x_1383_, v___x_1384_);
lean_dec_ref(v___x_1383_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_arg_1376_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = l_Lean_Expr_cleanupAnnotations(v_arg_1376_);
v___x_1388_ = l_Lean_Expr_isApp(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v___x_1387_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1387_);
v___x_1391_ = l_Lean_Expr_isApp(v___x_1390_);
if (v___x_1391_ == 0)
{
lean_dec_ref(v___x_1390_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v_arg_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_arg_1393_ = lean_ctor_get(v___x_1390_, 1);
lean_inc_ref(v_arg_1393_);
v___x_1394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1390_);
v___x_1395_ = l_Lean_Expr_isApp(v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec_ref(v___x_1394_);
lean_dec_ref(v_arg_1393_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1394_);
v___x_1398_ = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
v___x_1399_ = l_Lean_Expr_isConstOf(v___x_1397_, v___x_1398_);
lean_dec_ref(v___x_1397_);
if (v___x_1399_ == 0)
{
lean_dec_ref(v_arg_1393_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Meta_getNatValue_x3f(v_arg_1393_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
lean_dec_ref(v_arg_1393_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1421_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1421_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1421_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
if (lean_obj_tag(v_a_1402_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_m_1362_);
v_val_1406_ = lean_ctor_get(v_a_1402_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_a_1402_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1408_ = v_a_1402_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_val_1406_);
lean_dec(v_a_1402_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_x_1367_);
lean_ctor_set(v___x_1369_, 0, v_val_1406_);
v___x_1411_ = v___x_1369_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_val_1406_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_x_1367_);
v___x_1411_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1413_);
v___x_1415_ = v___x_1404_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
else
{
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
v_m_1346_ = v_m_1362_;
goto _start;
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_del_object(v___x_1369_);
lean_dec(v_x_1367_);
lean_dec(v_m_1362_);
v_a_1422_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1401_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1401_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
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
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_m_1362_);
lean_dec_ref(v_p_1361_);
v_a_1437_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1363_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1363_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_m_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* v_p_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (lean_obj_tag(v_p_1459_) == 0)
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
v_isSharedCheck_1479_ = !lean_is_exclusive(v_p_1459_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_p_1459_, 0);
lean_dec(v_unused_1480_);
v___x_1473_ = v_p_1459_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v_p_1459_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_box(0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_v_1481_; lean_object* v_p_1482_; lean_object* v___x_1483_; 
v_v_1481_ = lean_ctor_get(v_p_1459_, 1);
lean_inc(v_v_1481_);
v_p_1482_ = lean_ctor_get(v_p_1459_, 2);
lean_inc_ref(v_p_1482_);
lean_dec_ref_known(v_p_1459_, 3);
v___x_1483_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(v_v_1481_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
if (lean_obj_tag(v_a_1484_) == 1)
{
lean_dec_ref_known(v_a_1484_, 1);
lean_dec_ref(v_p_1482_);
return v___x_1483_;
}
else
{
lean_dec(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v_p_1459_ = v_p_1482_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_1482_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* v_p_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(lean_object* v_k_u2082_x27_1500_, lean_object* v_m_u2082_1501_, lean_object* v_p_u2082_1502_, lean_object* v_p_u2081_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
if (lean_obj_tag(v_p_u2081_1503_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref_known(v_p_u2081_1503_, 1);
lean_dec_ref(v_p_u2082_1502_);
lean_dec(v_m_u2082_1501_);
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
else
{
lean_object* v_k_1518_; lean_object* v_v_1519_; lean_object* v_p_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1656_; 
v_k_1518_ = lean_ctor_get(v_p_u2081_1503_, 0);
v_v_1519_ = lean_ctor_get(v_p_u2081_1503_, 1);
v_p_1520_ = lean_ctor_get(v_p_u2081_1503_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_p_u2081_1503_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1522_ = v_p_u2081_1503_;
v_isShared_1523_ = v_isSharedCheck_1656_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_p_1520_);
lean_inc(v_v_1519_);
lean_inc(v_k_1518_);
lean_dec(v_p_u2081_1503_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1656_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_1501_, v_v_1519_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1500_, v_m_u2082_1501_, v_p_u2082_1502_, v_p_1520_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1608_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1608_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1608_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
if (lean_obj_tag(v_a_1526_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1531_; 
lean_del_object(v___x_1528_);
v_val_1530_ = lean_ctor_get(v_a_1526_, 0);
lean_inc(v_val_1530_);
v___x_1531_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1595_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1595_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1595_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
if (lean_obj_tag(v_a_1532_) == 1)
{
lean_object* v_val_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1568_; 
v_val_1536_ = lean_ctor_get(v_a_1532_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1532_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1538_ = v_a_1532_;
v_isShared_1539_ = v_isSharedCheck_1568_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_val_1536_);
lean_dec(v_a_1532_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1568_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_p_1540_; lean_object* v_k_u2081_1541_; lean_object* v_k_u2082_1542_; lean_object* v_m_u2082_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1567_; 
v_p_1540_ = lean_ctor_get(v_val_1530_, 0);
v_k_u2081_1541_ = lean_ctor_get(v_val_1530_, 1);
v_k_u2082_1542_ = lean_ctor_get(v_val_1530_, 2);
v_m_u2082_1543_ = lean_ctor_get(v_val_1530_, 3);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1545_ = v_val_1530_;
v_isShared_1546_ = v_isSharedCheck_1567_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_m_u2082_1543_);
lean_inc(v_k_u2082_1542_);
lean_inc(v_k_u2081_1541_);
lean_inc(v_p_1540_);
lean_dec(v_val_1530_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1567_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1547_ = lean_int_mul(v_k_1518_, v_k_u2081_1541_);
lean_dec(v_k_1518_);
v___x_1548_ = lean_nat_to_int(v_val_1536_);
v___x_1549_ = lean_int_emod(v___x_1547_, v___x_1548_);
lean_dec(v___x_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
v___x_1551_ = lean_int_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref_known(v_a_1526_, 1);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 2, v_p_1540_);
lean_ctor_set(v___x_1522_, 0, v___x_1549_);
v___x_1553_ = v___x_1522_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_v_1519_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_p_1540_);
v___x_1553_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1553_);
v___x_1555_ = v___x_1545_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_u2081_1541_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_k_u2082_1542_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_m_u2082_1543_);
v___x_1555_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1555_);
v___x_1557_ = v___x_1538_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1557_);
v___x_1559_ = v___x_1534_;
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
lean_object* v___x_1565_; 
lean_dec(v___x_1549_);
lean_del_object(v___x_1545_);
lean_dec(v_m_u2082_1543_);
lean_dec(v_k_u2082_1542_);
lean_dec(v_k_u2081_1541_);
lean_dec_ref(v_p_1540_);
lean_del_object(v___x_1538_);
lean_del_object(v___x_1522_);
lean_dec(v_v_1519_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v_a_1526_);
v___x_1565_ = v___x_1534_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1526_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_a_1532_);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_a_1526_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_a_1526_, 0);
lean_dec(v_unused_1594_);
v___x_1570_ = v_a_1526_;
v_isShared_1571_ = v_isSharedCheck_1593_;
goto v_resetjp_1569_;
}
else
{
lean_dec(v_a_1526_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1593_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_p_1572_; lean_object* v_k_u2081_1573_; lean_object* v_k_u2082_1574_; lean_object* v_m_u2082_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1592_; 
v_p_1572_ = lean_ctor_get(v_val_1530_, 0);
v_k_u2081_1573_ = lean_ctor_get(v_val_1530_, 1);
v_k_u2082_1574_ = lean_ctor_get(v_val_1530_, 2);
v_m_u2082_1575_ = lean_ctor_get(v_val_1530_, 3);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1577_ = v_val_1530_;
v_isShared_1578_ = v_isSharedCheck_1592_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_m_u2082_1575_);
lean_inc(v_k_u2082_1574_);
lean_inc(v_k_u2081_1573_);
lean_inc(v_p_1572_);
lean_dec(v_val_1530_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1592_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_int_mul(v_k_1518_, v_k_u2081_1573_);
lean_dec(v_k_1518_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 2, v_p_1572_);
lean_ctor_set(v___x_1522_, 0, v___x_1579_);
v___x_1581_ = v___x_1522_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_v_1519_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_p_1572_);
v___x_1581_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_u2081_1573_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_k_u2082_1574_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_m_u2082_1575_);
v___x_1583_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1583_);
v___x_1585_ = v___x_1570_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1585_);
v___x_1587_ = v___x_1534_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
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
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref_known(v_a_1526_, 1);
lean_dec(v_val_1530_);
lean_del_object(v___x_1522_);
lean_dec(v_v_1519_);
lean_dec(v_k_1518_);
v_a_1596_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1531_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1531_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_dec(v_a_1526_);
lean_del_object(v___x_1522_);
lean_dec(v_v_1519_);
lean_dec(v_k_1518_);
v___x_1604_ = lean_box(0);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1604_);
v___x_1606_ = v___x_1528_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_del_object(v___x_1522_);
lean_dec(v_v_1519_);
lean_dec(v_k_1518_);
return v___x_1525_;
}
}
else
{
lean_object* v_m_u2082_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_g_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_k_u2082_1615_; lean_object* v___x_1616_; 
lean_del_object(v___x_1522_);
v_m_u2082_1609_ = l_Lean_Grind_CommRing_Mon_div(v_v_1519_, v_m_u2082_1501_);
v___x_1610_ = lean_nat_abs(v_k_1518_);
v___x_1611_ = lean_nat_abs(v_k_u2082_x27_1500_);
v_g_1612_ = lean_nat_gcd(v___x_1610_, v___x_1611_);
lean_dec(v___x_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_nat_to_int(v_g_1612_);
v___x_1614_ = lean_int_neg(v_k_1518_);
lean_dec(v_k_1518_);
v_k_u2082_1615_ = lean_int_ediv(v___x_1614_, v___x_1613_);
lean_dec(v___x_1614_);
lean_inc(v_m_u2082_1609_);
v___x_1616_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_u2082_1615_, v_m_u2082_1609_, v_p_u2082_1502_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v_k_u2081_1618_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v_k_u2081_1618_ = lean_int_ediv(v_k_u2082_x27_1500_, v___x_1613_);
lean_dec(v___x_1613_);
v___x_1619_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_u2081_1618_, v_p_1520_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
lean_inc_ref(v_a_1513_);
v___x_1621_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_1617_, v_a_1620_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1631_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1626_, 0, v_a_1622_);
lean_ctor_set(v___x_1626_, 1, v_k_u2081_1618_);
lean_ctor_set(v___x_1626_, 2, v_k_u2082_1615_);
lean_ctor_set(v___x_1626_, 3, v_m_u2082_1609_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_k_u2081_1618_);
lean_dec(v_k_u2082_1615_);
lean_dec(v_m_u2082_1609_);
v_a_1632_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1621_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1621_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_k_u2081_1618_);
lean_dec(v_a_1617_);
lean_dec(v_k_u2082_1615_);
lean_dec(v_m_u2082_1609_);
v_a_1640_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1619_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1619_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_k_u2082_1615_);
lean_dec(v___x_1613_);
lean_dec(v_m_u2082_1609_);
lean_dec_ref(v_p_1520_);
v_a_1648_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1616_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1616_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(lean_object* v_k_u2082_x27_1657_, lean_object* v_m_u2082_1658_, lean_object* v_p_u2082_1659_, lean_object* v_p_u2081_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_1657_, v_m_u2082_1658_, v_p_u2082_1659_, v_p_u2081_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_k_u2082_x27_1657_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f(lean_object* v_p_u2081_1674_, lean_object* v_p_u2082_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
if (lean_obj_tag(v_p_u2082_1675_) == 1)
{
lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v_p_1690_; lean_object* v___x_1691_; 
v_k_1688_ = lean_ctor_get(v_p_u2082_1675_, 0);
lean_inc(v_k_1688_);
v_v_1689_ = lean_ctor_get(v_p_u2082_1675_, 1);
lean_inc(v_v_1689_);
v_p_1690_ = lean_ctor_get(v_p_u2082_1675_, 2);
lean_inc_ref(v_p_1690_);
lean_dec_ref_known(v_p_u2082_1675_, 3);
v___x_1691_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_1688_, v_v_1689_, v_p_1690_, v_p_u2081_1674_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_k_1688_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref(v_p_u2082_1675_);
lean_dec_ref(v_p_u2081_1674_);
v___x_1692_ = lean_box(0);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(lean_object* v_p_u2081_1694_, lean_object* v_p_u2082_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(v_p_u2081_1694_, v_p_u2082_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1708_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
