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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value;
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1;
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
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
lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_37; 
x_17 = lean_ctor_get(x_16, 0);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
x_18 = x_16;
x_19 = x_37;
goto block_36;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 5);
lean_inc(x_21);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_35; 
x_22 = lean_ctor_get(x_21, 0);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
x_23 = x_21;
x_24 = x_35;
goto block_34;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_28 = x_23;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_25);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_28);
x_29 = x_18;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
else
{
lean_dec(x_25);
lean_del_object(x_23);
lean_del_object(x_18);
goto block_15;
}
}
}
else
{
lean_dec(x_21);
lean_del_object(x_18);
goto block_15;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = lean_ctor_get(x_16, 0);
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
x_39 = x_16;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_16 = x_14;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_int_emod(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_20);
x_21 = x_16;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; 
lean_dec(x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_1);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_30 = x_14;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_29; 
x_16 = lean_ctor_get(x_15, 0);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
x_17 = x_15;
x_18 = x_29;
goto block_28;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_29;
goto block_28;
}
block_28:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Grind_CommRing_Poly_addConstC(x_1, x_2, x_19);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_20);
x_21 = x_17;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = l_Lean_Grind_CommRing_Poly_addConst(x_1, x_2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_24);
x_25 = x_17;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_15, 0);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
x_31 = x_15;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_29; 
x_16 = lean_ctor_get(x_15, 0);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
x_17 = x_15;
x_18 = x_29;
goto block_28;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_29;
goto block_28;
}
block_28:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Grind_CommRing_Poly_mulConstC(x_1, x_2, x_19);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_20);
x_21 = x_17;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = l_Lean_Grind_CommRing_Poly_mulConst(x_1, x_2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_24);
x_25 = x_17;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec_ref(x_2);
x_30 = lean_ctor_get(x_15, 0);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
x_31 = x_15;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_30; 
x_17 = lean_ctor_get(x_16, 0);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
x_18 = x_16;
x_19 = x_30;
goto block_29;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_30;
goto block_29;
}
block_29:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = l_Lean_Grind_CommRing_Poly_mulMonC(x_1, x_2, x_3, x_20);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = l_Lean_Grind_CommRing_Poly_mulMon(x_1, x_2, x_3);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_25);
x_26 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_16, 0);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
x_32 = x_16;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_150; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 2);
x_18 = lean_ctor_get(x_12, 3);
x_19 = lean_ctor_get(x_12, 4);
x_20 = lean_ctor_get(x_12, 5);
x_21 = lean_ctor_get(x_12, 6);
x_22 = lean_ctor_get(x_12, 7);
x_23 = lean_ctor_get(x_12, 8);
x_24 = lean_ctor_get(x_12, 9);
x_25 = lean_ctor_get(x_12, 10);
x_26 = lean_ctor_get(x_12, 11);
x_27 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_28 = lean_ctor_get(x_12, 12);
x_29 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_30 = lean_ctor_get(x_12, 13);
x_150 = !lean_is_exclusive(x_12);
if (x_150 == 0)
{
x_31 = x_12;
x_32 = x_150;
goto block_149;
}
else
{
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = x_150;
goto block_149;
}
block_149:
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_18, x_19);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_18, x_34);
lean_dec(x_18);
if (x_32 == 0)
{
lean_ctor_set(x_31, 3, x_35);
x_36 = x_31;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_147, 0, x_15);
lean_ctor_set(x_147, 1, x_16);
lean_ctor_set(x_147, 2, x_17);
lean_ctor_set(x_147, 3, x_35);
lean_ctor_set(x_147, 4, x_19);
lean_ctor_set(x_147, 5, x_20);
lean_ctor_set(x_147, 6, x_21);
lean_ctor_set(x_147, 7, x_22);
lean_ctor_set(x_147, 8, x_23);
lean_ctor_set(x_147, 9, x_24);
lean_ctor_set(x_147, 10, x_25);
lean_ctor_set(x_147, 11, x_26);
lean_ctor_set(x_147, 12, x_28);
lean_ctor_set(x_147, 13, x_30);
lean_ctor_set_uint8(x_147, sizeof(void*)*14, x_27);
lean_ctor_set_uint8(x_147, sizeof(void*)*14 + 1, x_29);
x_36 = x_147;
goto block_146;
}
block_146:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_2, 0);
x_63 = !lean_is_exclusive(x_2);
if (x_63 == 0)
{
x_39 = x_2;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_int_add(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
lean_dec_ref(x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_53; 
x_43 = lean_ctor_get(x_42, 0);
x_53 = !lean_is_exclusive(x_42);
if (x_53 == 0)
{
x_44 = x_42;
x_45 = x_53;
goto block_52;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_46; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_43);
x_46 = x_39;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_43);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_47 = x_44;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_del_object(x_39);
x_54 = lean_ctor_get(x_42, 0);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
x_55 = x_42;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec_ref(x_1);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_2, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
lean_dec_ref(x_36);
lean_dec(x_64);
return x_65;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_dec_ref(x_2);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
lean_dec_ref(x_36);
lean_dec(x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_68 = lean_ctor_get(x_1, 0);
x_69 = lean_ctor_get(x_1, 1);
x_70 = lean_ctor_get(x_1, 2);
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_ctor_get(x_2, 2);
x_74 = l_Lean_Grind_CommRing_Mon_grevlex(x_69, x_72);
switch (x_74) {
case 0:
{
lean_object* x_75; uint8_t x_76; uint8_t x_90; 
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_90 = !lean_is_exclusive(x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_2, 2);
lean_dec(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_2, 0);
lean_dec(x_93);
x_75 = x_2;
x_76 = x_90;
goto block_89;
}
else
{
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_77; 
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_1, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_88; 
x_78 = lean_ctor_get(x_77, 0);
x_88 = !lean_is_exclusive(x_77);
if (x_88 == 0)
{
x_79 = x_77;
x_80 = x_88;
goto block_87;
}
else
{
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_81; 
if (x_76 == 0)
{
lean_ctor_set(x_75, 2, x_78);
x_81 = x_75;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_72);
lean_ctor_set(x_86, 2, x_78);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_80 == 0)
{
lean_ctor_set(x_79, 0, x_81);
x_82 = x_79;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_del_object(x_75);
lean_dec(x_72);
lean_dec(x_71);
return x_77;
}
}
}
case 1:
{
lean_object* x_94; uint8_t x_95; uint8_t x_123; 
lean_inc_ref(x_73);
lean_inc(x_71);
lean_inc_ref(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_2);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_2, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_2, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_2, 0);
lean_dec(x_126);
x_94 = x_2;
x_95 = x_123;
goto block_122;
}
else
{
lean_dec(x_2);
x_94 = lean_box(0);
x_95 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_int_add(x_68, x_71);
lean_dec(x_71);
lean_dec(x_68);
x_97 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
x_100 = lean_int_dec_eq(x_98, x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_70, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_112; 
x_102 = lean_ctor_get(x_101, 0);
x_112 = !lean_is_exclusive(x_101);
if (x_112 == 0)
{
x_103 = x_101;
x_104 = x_112;
goto block_111;
}
else
{
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_105; 
if (x_95 == 0)
{
lean_ctor_set(x_94, 2, x_102);
lean_ctor_set(x_94, 1, x_69);
lean_ctor_set(x_94, 0, x_98);
x_105 = x_94;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_69);
lean_ctor_set(x_110, 2, x_102);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_104 == 0)
{
lean_ctor_set(x_103, 0, x_105);
x_106 = x_103;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_dec(x_98);
lean_del_object(x_94);
lean_dec(x_69);
return x_101;
}
}
else
{
lean_dec(x_98);
lean_del_object(x_94);
lean_dec(x_69);
x_1 = x_70;
x_2 = x_73;
x_12 = x_36;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_del_object(x_94);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec_ref(x_36);
x_114 = lean_ctor_get(x_97, 0);
x_121 = !lean_is_exclusive(x_97);
if (x_121 == 0)
{
x_115 = x_97;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_97);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
}
default: 
{
lean_object* x_127; uint8_t x_128; uint8_t x_142; 
lean_inc_ref(x_70);
lean_inc(x_69);
lean_inc(x_68);
x_142 = !lean_is_exclusive(x_1);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_1, 2);
lean_dec(x_143);
x_144 = lean_ctor_get(x_1, 1);
lean_dec(x_144);
x_145 = lean_ctor_get(x_1, 0);
lean_dec(x_145);
x_127 = x_1;
x_128 = x_142;
goto block_141;
}
else
{
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_129; 
x_129 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_140; 
x_130 = lean_ctor_get(x_129, 0);
x_140 = !lean_is_exclusive(x_129);
if (x_140 == 0)
{
x_131 = x_129;
x_132 = x_140;
goto block_139;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_133; 
if (x_128 == 0)
{
lean_ctor_set(x_127, 2, x_130);
x_133 = x_127;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_68);
lean_ctor_set(x_138, 1, x_69);
lean_ctor_set(x_138, 2, x_130);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_133);
x_134 = x_131;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_133);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_del_object(x_127);
lean_dec(x_69);
lean_dec(x_68);
return x_129;
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
lean_object* x_148; 
lean_del_object(x_31);
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_20);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_4(x_4, x_10, x_11, x_12, x_13);
return x_14;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec_ref(x_2);
x_19 = lean_apply_4(x_5, x_15, x_16, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_25);
lean_dec_ref(x_2);
x_26 = lean_apply_6(x_6, x_20, x_21, x_22, x_23, x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_64; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 2);
x_19 = lean_ctor_get(x_13, 3);
x_20 = lean_ctor_get(x_13, 4);
x_21 = lean_ctor_get(x_13, 5);
x_22 = lean_ctor_get(x_13, 6);
x_23 = lean_ctor_get(x_13, 7);
x_24 = lean_ctor_get(x_13, 8);
x_25 = lean_ctor_get(x_13, 9);
x_26 = lean_ctor_get(x_13, 10);
x_27 = lean_ctor_get(x_13, 11);
x_28 = lean_ctor_get_uint8(x_13, sizeof(void*)*14);
x_29 = lean_ctor_get(x_13, 12);
x_30 = lean_ctor_get_uint8(x_13, sizeof(void*)*14 + 1);
x_31 = lean_ctor_get(x_13, 13);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
x_32 = x_13;
x_33 = x_64;
goto block_63;
}
else
{
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
x_32 = lean_box(0);
x_33 = x_64;
goto block_63;
}
block_63:
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_19, x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_19, x_35);
lean_dec(x_19);
if (x_33 == 0)
{
lean_ctor_set(x_32, 3, x_36);
x_37 = x_32;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_61, 0, x_16);
lean_ctor_set(x_61, 1, x_17);
lean_ctor_set(x_61, 2, x_18);
lean_ctor_set(x_61, 3, x_36);
lean_ctor_set(x_61, 4, x_20);
lean_ctor_set(x_61, 5, x_21);
lean_ctor_set(x_61, 6, x_22);
lean_ctor_set(x_61, 7, x_23);
lean_ctor_set(x_61, 8, x_24);
lean_ctor_set(x_61, 9, x_25);
lean_ctor_set(x_61, 10, x_26);
lean_ctor_set(x_61, 11, x_27);
lean_ctor_set(x_61, 12, x_29);
lean_ctor_set(x_61, 13, x_31);
lean_ctor_set_uint8(x_61, sizeof(void*)*14, x_28);
lean_ctor_set_uint8(x_61, sizeof(void*)*14 + 1, x_30);
x_37 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec_ref(x_2);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_38, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37, x_14);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_3, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37, x_14);
return x_41;
}
else
{
lean_dec_ref(x_37);
lean_dec_ref(x_3);
return x_39;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_44);
lean_dec_ref(x_2);
x_45 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
x_46 = l_Lean_Core_checkSystem(x_45, x_37, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec_ref(x_46);
lean_inc_ref(x_1);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_42, x_43, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37, x_14);
lean_dec(x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc_ref(x_37);
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_3, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37, x_14);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_2 = x_44;
x_3 = x_50;
x_13 = x_37;
goto _start;
}
else
{
lean_dec_ref(x_44);
lean_dec_ref(x_37);
lean_dec_ref(x_1);
return x_49;
}
}
else
{
lean_dec_ref(x_44);
lean_dec_ref(x_37);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_47;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_37);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_46, 0);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
x_53 = x_46;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
else
{
lean_object* x_62; 
lean_del_object(x_32);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_21);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(x_2, x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_57; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 2);
x_18 = lean_ctor_get(x_12, 3);
x_19 = lean_ctor_get(x_12, 4);
x_20 = lean_ctor_get(x_12, 5);
x_21 = lean_ctor_get(x_12, 6);
x_22 = lean_ctor_get(x_12, 7);
x_23 = lean_ctor_get(x_12, 8);
x_24 = lean_ctor_get(x_12, 9);
x_25 = lean_ctor_get(x_12, 10);
x_26 = lean_ctor_get(x_12, 11);
x_27 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_28 = lean_ctor_get(x_12, 12);
x_29 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_30 = lean_ctor_get(x_12, 13);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
x_31 = x_12;
x_32 = x_57;
goto block_56;
}
else
{
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = x_57;
goto block_56;
}
block_56:
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_18, x_19);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_2, x_34);
if (x_35 == 1)
{
lean_object* x_36; lean_object* x_37; 
lean_del_object(x_31);
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_1);
x_36 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_2, x_38);
x_40 = lean_nat_dec_eq(x_39, x_34);
if (x_40 == 1)
{
lean_object* x_41; 
lean_dec(x_39);
lean_del_object(x_31);
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_1);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_sub(x_39, x_38);
lean_dec(x_39);
x_43 = lean_nat_add(x_18, x_38);
lean_dec(x_18);
if (x_32 == 0)
{
lean_ctor_set(x_31, 3, x_43);
x_44 = x_31;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_54, 0, x_15);
lean_ctor_set(x_54, 1, x_16);
lean_ctor_set(x_54, 2, x_17);
lean_ctor_set(x_54, 3, x_43);
lean_ctor_set(x_54, 4, x_19);
lean_ctor_set(x_54, 5, x_20);
lean_ctor_set(x_54, 6, x_21);
lean_ctor_set(x_54, 7, x_22);
lean_ctor_set(x_54, 8, x_23);
lean_ctor_set(x_54, 9, x_24);
lean_ctor_set(x_54, 10, x_25);
lean_ctor_set(x_54, 11, x_26);
lean_ctor_set(x_54, 12, x_28);
lean_ctor_set(x_54, 13, x_30);
lean_ctor_set_uint8(x_54, sizeof(void*)*14, x_27);
lean_ctor_set_uint8(x_54, sizeof(void*)*14 + 1, x_29);
x_44 = x_54;
goto block_53;
}
block_53:
{
uint8_t x_45; 
x_45 = lean_nat_dec_eq(x_42, x_34);
if (x_45 == 1)
{
lean_object* x_46; 
lean_dec(x_42);
lean_inc_ref(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44, x_13);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_nat_sub(x_42, x_38);
lean_dec(x_42);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_47);
lean_inc_ref(x_44);
lean_inc_ref(x_1);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_1, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44, x_13);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44, x_13);
return x_52;
}
else
{
lean_dec_ref(x_44);
lean_dec_ref(x_1);
return x_50;
}
}
}
}
}
}
else
{
lean_object* x_55; 
lean_del_object(x_31);
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_1);
x_55 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_20);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_72; 
x_46 = lean_ctor_get(x_1, 0);
x_72 = !lean_is_exclusive(x_1);
if (x_72 == 0)
{
x_47 = x_1;
x_48 = x_72;
goto block_71;
}
else
{
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_to_int(x_46);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_62; 
x_51 = lean_ctor_get(x_50, 0);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
x_52 = x_50;
x_53 = x_62;
goto block_61;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_54; 
if (x_48 == 0)
{
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_51);
x_54 = x_47;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_51);
x_54 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_55);
x_56 = x_52;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_del_object(x_47);
x_63 = lean_ctor_get(x_50, 0);
x_70 = !lean_is_exclusive(x_50);
if (x_70 == 0)
{
x_64 = x_50;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_50);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
case 3:
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_82; 
lean_dec_ref(x_11);
x_73 = lean_ctor_get(x_1, 0);
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
x_74 = x_1;
x_75 = x_82;
goto block_81;
}
else
{
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Grind_CommRing_Poly_ofVar(x_73);
if (x_75 == 0)
{
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_76);
x_77 = x_74;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_76);
x_77 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
case 4:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_83);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_84 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_11);
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_111; 
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
x_111 = !lean_is_exclusive(x_85);
if (x_111 == 0)
{
x_87 = x_85;
x_88 = x_111;
goto block_110;
}
else
{
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_box(0);
x_88 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_89, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_101; 
x_91 = lean_ctor_get(x_90, 0);
x_101 = !lean_is_exclusive(x_90);
if (x_101 == 0)
{
x_92 = x_90;
x_93 = x_101;
goto block_100;
}
else
{
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_94; 
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_91);
x_94 = x_87;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_91);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_93 == 0)
{
lean_ctor_set(x_92, 0, x_94);
x_95 = x_92;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_94);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_del_object(x_87);
x_102 = lean_ctor_get(x_90, 0);
x_109 = !lean_is_exclusive(x_90);
if (x_109 == 0)
{
x_103 = x_90;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
}
else
{
lean_dec_ref(x_11);
return x_84;
}
}
case 5:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_113);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_114 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_dec_ref(x_113);
lean_dec_ref(x_11);
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
lean_inc_ref(x_11);
x_117 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_dec(x_116);
lean_dec_ref(x_11);
return x_117;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_143; 
lean_dec_ref(x_117);
x_119 = lean_ctor_get(x_118, 0);
x_143 = !lean_is_exclusive(x_118);
if (x_143 == 0)
{
x_120 = x_118;
x_121 = x_143;
goto block_142;
}
else
{
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_box(0);
x_121 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_122; 
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_116, x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_133; 
x_123 = lean_ctor_get(x_122, 0);
x_133 = !lean_is_exclusive(x_122);
if (x_133 == 0)
{
x_124 = x_122;
x_125 = x_133;
goto block_132;
}
else
{
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_box(0);
x_125 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_126; 
if (x_121 == 0)
{
lean_ctor_set(x_120, 0, x_123);
x_126 = x_120;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_123);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_125 == 0)
{
lean_ctor_set(x_124, 0, x_126);
x_127 = x_124;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_126);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_141; 
lean_del_object(x_120);
x_134 = lean_ctor_get(x_122, 0);
x_141 = !lean_is_exclusive(x_122);
if (x_141 == 0)
{
x_135 = x_122;
x_136 = x_141;
goto block_140;
}
else
{
lean_inc(x_134);
lean_dec(x_122);
x_135 = lean_box(0);
x_136 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_137; 
if (x_136 == 0)
{
x_137 = x_135;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_134);
x_137 = x_139;
goto block_138;
}
block_138:
{
return x_137;
}
}
}
}
}
}
else
{
lean_dec(x_116);
lean_dec_ref(x_11);
return x_117;
}
}
}
else
{
lean_dec_ref(x_113);
lean_dec_ref(x_11);
return x_114;
}
}
case 6:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_145);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_144, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_dec_ref(x_145);
lean_dec_ref(x_11);
return x_146;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec_ref(x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
lean_inc_ref(x_11);
x_149 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_dec(x_148);
lean_dec_ref(x_11);
return x_149;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_186; 
lean_dec_ref(x_149);
x_151 = lean_ctor_get(x_150, 0);
x_186 = !lean_is_exclusive(x_150);
if (x_186 == 0)
{
x_152 = x_150;
x_153 = x_186;
goto block_185;
}
else
{
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
x_155 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_154, x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_148, x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_168; 
x_158 = lean_ctor_get(x_157, 0);
x_168 = !lean_is_exclusive(x_157);
if (x_168 == 0)
{
x_159 = x_157;
x_160 = x_168;
goto block_167;
}
else
{
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_box(0);
x_160 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_161; 
if (x_153 == 0)
{
lean_ctor_set(x_152, 0, x_158);
x_161 = x_152;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_158);
x_161 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_162; 
if (x_160 == 0)
{
lean_ctor_set(x_159, 0, x_161);
x_162 = x_159;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_161);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_176; 
lean_del_object(x_152);
x_169 = lean_ctor_get(x_157, 0);
x_176 = !lean_is_exclusive(x_157);
if (x_176 == 0)
{
x_170 = x_157;
x_171 = x_176;
goto block_175;
}
else
{
lean_inc(x_169);
lean_dec(x_157);
x_170 = lean_box(0);
x_171 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_172; 
if (x_171 == 0)
{
x_172 = x_170;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_169);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_184; 
lean_del_object(x_152);
lean_dec(x_148);
lean_dec_ref(x_11);
x_177 = lean_ctor_get(x_155, 0);
x_184 = !lean_is_exclusive(x_155);
if (x_184 == 0)
{
x_178 = x_155;
x_179 = x_184;
goto block_183;
}
else
{
lean_inc(x_177);
lean_dec(x_155);
x_178 = lean_box(0);
x_179 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_180; 
if (x_179 == 0)
{
x_180 = x_178;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_177);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
}
}
else
{
lean_dec(x_148);
lean_dec_ref(x_11);
return x_149;
}
}
}
else
{
lean_dec_ref(x_145);
lean_dec_ref(x_11);
return x_146;
}
}
case 7:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_188);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_189 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
lean_dec_ref(x_188);
lean_dec_ref(x_11);
return x_189;
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
lean_inc_ref(x_11);
x_192 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_dec(x_191);
lean_dec_ref(x_11);
return x_192;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_218; 
lean_dec_ref(x_192);
x_194 = lean_ctor_get(x_193, 0);
x_218 = !lean_is_exclusive(x_193);
if (x_218 == 0)
{
x_195 = x_193;
x_196 = x_218;
goto block_217;
}
else
{
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_box(0);
x_196 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_197; 
x_197 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_191, x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_208; 
x_198 = lean_ctor_get(x_197, 0);
x_208 = !lean_is_exclusive(x_197);
if (x_208 == 0)
{
x_199 = x_197;
x_200 = x_208;
goto block_207;
}
else
{
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_box(0);
x_200 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_201; 
if (x_196 == 0)
{
lean_ctor_set(x_195, 0, x_198);
x_201 = x_195;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_198);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_200 == 0)
{
lean_ctor_set(x_199, 0, x_201);
x_202 = x_199;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_201);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_216; 
lean_del_object(x_195);
x_209 = lean_ctor_get(x_197, 0);
x_216 = !lean_is_exclusive(x_197);
if (x_216 == 0)
{
x_210 = x_197;
x_211 = x_216;
goto block_215;
}
else
{
lean_inc(x_209);
lean_dec(x_197);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
}
}
}
else
{
lean_dec(x_191);
lean_dec_ref(x_11);
return x_192;
}
}
}
else
{
lean_dec_ref(x_188);
lean_dec_ref(x_11);
return x_189;
}
}
case 8:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_316; 
x_219 = lean_ctor_get(x_1, 0);
x_220 = lean_ctor_get(x_1, 1);
x_316 = !lean_is_exclusive(x_1);
if (x_316 == 0)
{
x_221 = x_1;
x_222 = x_316;
goto block_315;
}
else
{
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_1);
x_221 = lean_box(0);
x_222 = x_316;
goto block_315;
}
block_315:
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_nat_dec_eq(x_220, x_223);
if (x_224 == 0)
{
switch (lean_obj_tag(x_219)) {
case 0:
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_270; 
lean_del_object(x_221);
x_225 = lean_ctor_get(x_219, 0);
x_270 = !lean_is_exclusive(x_219);
if (x_270 == 0)
{
x_226 = x_219;
x_227 = x_270;
goto block_269;
}
else
{
lean_inc(x_225);
lean_dec(x_219);
x_226 = lean_box(0);
x_227 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_228; 
lean_inc(x_220);
x_228 = l_Lean_Meta_Grind_Arith_checkExp(x_220, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_260; 
x_229 = lean_ctor_get(x_228, 0);
x_260 = !lean_is_exclusive(x_228);
if (x_260 == 0)
{
x_230 = x_228;
x_231 = x_260;
goto block_259;
}
else
{
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_box(0);
x_231 = x_260;
goto block_259;
}
block_259:
{
if (lean_obj_tag(x_229) == 0)
{
if (x_224 == 0)
{
lean_object* x_255; lean_object* x_256; 
lean_del_object(x_226);
lean_dec(x_225);
lean_dec(x_220);
lean_dec_ref(x_11);
x_255 = lean_box(0);
if (x_231 == 0)
{
lean_ctor_set(x_230, 0, x_255);
x_256 = x_230;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_255);
x_256 = x_258;
goto block_257;
}
block_257:
{
return x_256;
}
}
else
{
lean_del_object(x_230);
goto block_254;
}
}
else
{
lean_dec_ref(x_229);
lean_del_object(x_230);
goto block_254;
}
block_254:
{
lean_object* x_232; lean_object* x_233; 
x_232 = l_Int_pow(x_225, x_220);
lean_dec(x_220);
lean_dec(x_225);
x_233 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_232, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_245; 
x_234 = lean_ctor_get(x_233, 0);
x_245 = !lean_is_exclusive(x_233);
if (x_245 == 0)
{
x_235 = x_233;
x_236 = x_245;
goto block_244;
}
else
{
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_box(0);
x_236 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_237; 
if (x_227 == 0)
{
lean_ctor_set(x_226, 0, x_234);
x_237 = x_226;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_234);
x_237 = x_243;
goto block_242;
}
block_242:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
if (x_236 == 0)
{
lean_ctor_set(x_235, 0, x_238);
x_239 = x_235;
goto block_240;
}
else
{
lean_object* x_241; 
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_238);
x_239 = x_241;
goto block_240;
}
block_240:
{
return x_239;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_253; 
lean_del_object(x_226);
x_246 = lean_ctor_get(x_233, 0);
x_253 = !lean_is_exclusive(x_233);
if (x_253 == 0)
{
x_247 = x_233;
x_248 = x_253;
goto block_252;
}
else
{
lean_inc(x_246);
lean_dec(x_233);
x_247 = lean_box(0);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_248 == 0)
{
x_249 = x_247;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_246);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_268; 
lean_del_object(x_226);
lean_dec(x_225);
lean_dec(x_220);
lean_dec_ref(x_11);
x_261 = lean_ctor_get(x_228, 0);
x_268 = !lean_is_exclusive(x_228);
if (x_268 == 0)
{
x_262 = x_228;
x_263 = x_268;
goto block_267;
}
else
{
lean_inc(x_261);
lean_dec(x_228);
x_262 = lean_box(0);
x_263 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_264; 
if (x_263 == 0)
{
x_264 = x_262;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_261);
x_264 = x_266;
goto block_265;
}
block_265:
{
return x_264;
}
}
}
}
}
case 3:
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_285; 
lean_dec_ref(x_11);
x_271 = lean_ctor_get(x_219, 0);
x_285 = !lean_is_exclusive(x_219);
if (x_285 == 0)
{
x_272 = x_219;
x_273 = x_285;
goto block_284;
}
else
{
lean_inc(x_271);
lean_dec(x_219);
x_272 = lean_box(0);
x_273 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_274; 
if (x_222 == 0)
{
lean_ctor_set_tag(x_221, 0);
lean_ctor_set(x_221, 0, x_271);
x_274 = x_221;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_271);
lean_ctor_set(x_283, 1, x_220);
x_274 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_box(0);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_Grind_CommRing_Poly_ofMon(x_276);
if (x_273 == 0)
{
lean_ctor_set_tag(x_272, 1);
lean_ctor_set(x_272, 0, x_277);
x_278 = x_272;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_277);
x_278 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
}
default: 
{
lean_object* x_286; 
lean_del_object(x_221);
lean_inc_ref(x_11);
x_286 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_219, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
lean_dec(x_220);
lean_dec_ref(x_11);
return x_286;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_312; 
lean_dec_ref(x_286);
x_288 = lean_ctor_get(x_287, 0);
x_312 = !lean_is_exclusive(x_287);
if (x_312 == 0)
{
x_289 = x_287;
x_290 = x_312;
goto block_311;
}
else
{
lean_inc(x_288);
lean_dec(x_287);
x_289 = lean_box(0);
x_290 = x_312;
goto block_311;
}
block_311:
{
lean_object* x_291; 
x_291 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_288, x_220, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_220);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_302; 
x_292 = lean_ctor_get(x_291, 0);
x_302 = !lean_is_exclusive(x_291);
if (x_302 == 0)
{
x_293 = x_291;
x_294 = x_302;
goto block_301;
}
else
{
lean_inc(x_292);
lean_dec(x_291);
x_293 = lean_box(0);
x_294 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_295; 
if (x_290 == 0)
{
lean_ctor_set(x_289, 0, x_292);
x_295 = x_289;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_292);
x_295 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_296; 
if (x_294 == 0)
{
lean_ctor_set(x_293, 0, x_295);
x_296 = x_293;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_295);
x_296 = x_298;
goto block_297;
}
block_297:
{
return x_296;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_310; 
lean_del_object(x_289);
x_303 = lean_ctor_get(x_291, 0);
x_310 = !lean_is_exclusive(x_291);
if (x_310 == 0)
{
x_304 = x_291;
x_305 = x_310;
goto block_309;
}
else
{
lean_inc(x_303);
lean_dec(x_291);
x_304 = lean_box(0);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_305 == 0)
{
x_306 = x_304;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_303);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
}
}
}
else
{
lean_dec(x_220);
lean_dec_ref(x_11);
return x_286;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_del_object(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_11);
x_313 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
}
}
default: 
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_1, 0);
lean_inc(x_317);
lean_dec_ref(x_1);
x_14 = x_317;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
goto block_45;
}
}
block_45:
{
lean_object* x_26; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_36; 
x_27 = lean_ctor_get(x_26, 0);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
x_28 = x_26;
x_29 = x_36;
goto block_35;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_31);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
x_37 = lean_ctor_get(x_26, 0);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
x_38 = x_26;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Grind_CommRing_Poly_mulConstM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_2, x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Grind_CommRing_Poly_mulMonM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Grind_CommRing_Poly_mulM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Grind_CommRing_Poly_combineM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_2);
lean_inc(x_22);
lean_inc(x_19);
x_24 = l_Lean_Grind_CommRing_Mon_lcm(x_19, x_22);
lean_inc(x_24);
x_25 = l_Lean_Grind_CommRing_Mon_div(x_24, x_19);
x_26 = lean_nat_abs(x_18);
x_27 = lean_nat_abs(x_21);
x_28 = lean_nat_gcd(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_int_ediv(x_21, x_29);
lean_dec(x_21);
lean_inc(x_25);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_30, x_25, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Grind_CommRing_Mon_div(x_24, x_22);
x_34 = lean_int_neg(x_18);
lean_dec(x_18);
x_35 = lean_int_ediv(x_34, x_29);
lean_dec(x_29);
lean_dec(x_34);
lean_inc(x_33);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_35, x_33, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_32, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_47; 
x_39 = lean_ctor_get(x_38, 0);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
x_40 = x_38;
x_41 = x_47;
goto block_46;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_25);
lean_ctor_set(x_42, 3, x_35);
lean_ctor_set(x_42, 4, x_33);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_42);
x_43 = x_40;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_25);
x_48 = lean_ctor_get(x_38, 0);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
x_49 = x_38;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
lean_dec_ref(x_12);
x_56 = lean_ctor_get(x_36, 0);
x_63 = !lean_is_exclusive(x_36);
if (x_63 == 0)
{
x_57 = x_36;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec_ref(x_12);
x_64 = lean_ctor_get(x_31, 0);
x_71 = !lean_is_exclusive(x_31);
if (x_71 == 0)
{
x_65 = x_31;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_31);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_12);
lean_dec_ref(x_2);
goto block_17;
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_17;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spolM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Grind_CommRing_Poly_spolM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_90; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 14);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_16, 0);
x_90 = !lean_is_exclusive(x_16);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_16, 1);
lean_dec(x_91);
x_23 = x_16;
x_24 = x_90;
goto block_89;
}
else
{
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_25; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_21, 2);
x_85 = l_Lean_instInhabitedExpr;
x_86 = lean_nat_dec_lt(x_22, x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec_ref(x_21);
x_87 = l_outOfBounds___redArg(x_85);
x_25 = x_87;
goto block_83;
}
else
{
lean_object* x_88; 
x_88 = l_Lean_PersistentArray_get_x21___redArg(x_85, x_21, x_22);
x_25 = x_88;
goto block_83;
}
block_83:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_cleanupAnnotations(x_25);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_29);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_37 = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_dec_ref(x_29);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Expr_cleanupAnnotations(x_29);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec_ref(x_40);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec_ref(x_43);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_46);
x_47 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Expr_appFnCleanup___redArg(x_47);
x_51 = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
x_52 = l_Lean_Expr_isConstOf(x_50, x_51);
lean_dec_ref(x_50);
if (x_52 == 0)
{
lean_dec_ref(x_46);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_54; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_54 = l_Lean_Meta_getNatValue_x3f(x_46, x_9, x_10, x_11, x_12);
lean_dec_ref(x_46);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_74; 
x_55 = lean_ctor_get(x_54, 0);
x_74 = !lean_is_exclusive(x_54);
if (x_74 == 0)
{
x_56 = x_54;
x_57 = x_74;
goto block_73;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_74;
goto block_73;
}
block_73:
{
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_71; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_58 = lean_ctor_get(x_55, 0);
x_71 = !lean_is_exclusive(x_55);
if (x_71 == 0)
{
x_59 = x_55;
x_60 = x_71;
goto block_70;
}
else
{
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_box(0);
x_60 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_61; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 0, x_58);
x_61 = x_23;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_22);
x_61 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_62; 
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_61);
x_62 = x_59;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_61);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_57 == 0)
{
lean_ctor_set(x_56, 0, x_62);
x_63 = x_56;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
else
{
lean_del_object(x_56);
lean_dec(x_55);
lean_del_object(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_del_object(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_75 = lean_ctor_get(x_54, 0);
x_82 = !lean_is_exclusive(x_54);
if (x_82 == 0)
{
x_76 = x_54;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_54);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
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
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_92 = lean_ctor_get(x_18, 0);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
x_93 = x_18;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_18);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_21; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_14 = x_1;
x_15 = x_21;
goto block_20;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_24);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_25 = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_25;
}
else
{
lean_dec(x_26);
lean_dec_ref(x_25);
x_1 = x_24;
goto _start;
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin)
;
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
}
#ifdef __cplusplus
}
#endif
