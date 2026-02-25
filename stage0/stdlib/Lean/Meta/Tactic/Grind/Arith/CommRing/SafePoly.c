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
lean_object* x_13; lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 5);
lean_inc(x_21);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 1)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_ctor_set(x_21, 0, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_dec(x_24);
lean_free_object(x_21);
lean_free_object(x_17);
x_13 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_dec(x_28);
lean_free_object(x_17);
x_13 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec(x_21);
lean_free_object(x_17);
x_13 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 5);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_37);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_dec(x_37);
lean_dec(x_36);
x_13 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_34);
x_13 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_emod(x_1, x_18);
lean_dec(x_18);
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_emod(x_1, x_22);
lean_dec(x_22);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Grind_CommRing_Poly_addConstC(x_1, x_2, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = l_Lean_Grind_CommRing_Poly_addConst(x_1, x_2);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Grind_CommRing_Poly_addConstC(x_1, x_2, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_25 = l_Lean_Grind_CommRing_Poly_addConst(x_1, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Grind_CommRing_Poly_mulConstC(x_1, x_2, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = l_Lean_Grind_CommRing_Poly_mulConst(x_1, x_2);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Grind_CommRing_Poly_mulConstC(x_1, x_2, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_25 = l_Lean_Grind_CommRing_Poly_mulConst(x_1, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
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
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Grind_CommRing_Poly_mulMonC(x_1, x_2, x_3, x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = l_Lean_Grind_CommRing_Poly_mulMon(x_1, x_2, x_3);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_Grind_CommRing_Poly_mulMonC(x_1, x_2, x_3, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
x_26 = l_Lean_Grind_CommRing_Poly_mulMon(x_1, x_2, x_3);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_19 = lean_ctor_get(x_12, 3);
x_20 = lean_ctor_get(x_12, 4);
x_21 = lean_ctor_get(x_12, 5);
x_22 = lean_ctor_get(x_12, 6);
x_23 = lean_ctor_get(x_12, 7);
x_24 = lean_ctor_get(x_12, 8);
x_25 = lean_ctor_get(x_12, 9);
x_26 = lean_ctor_get(x_12, 10);
x_27 = lean_ctor_get(x_12, 11);
x_28 = lean_ctor_get(x_12, 12);
x_29 = lean_ctor_get(x_12, 13);
x_30 = lean_nat_dec_eq(x_19, x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_19, x_31);
lean_dec(x_19);
lean_ctor_set(x_12, 3, x_32);
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_int_add(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
lean_ctor_set(x_2, 0, x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_2);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_2);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
lean_dec(x_2);
x_46 = lean_int_add(x_33, x_45);
lean_dec(x_45);
lean_dec(x_33);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_48);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_53 = x_47;
} else {
 lean_dec_ref(x_47);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec_ref(x_1);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_2, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_55);
return x_56;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec_ref(x_2);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_1, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
x_64 = lean_ctor_get(x_2, 2);
x_65 = l_Lean_Grind_CommRing_Mon_grevlex(x_60, x_63);
switch (x_65) {
case 0:
{
uint8_t x_66; 
lean_inc_ref(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_2, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_2, 0);
lean_dec(x_69);
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_ctor_set(x_2, 2, x_72);
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
lean_ctor_set(x_2, 2, x_73);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_2);
return x_74;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_63);
lean_dec(x_62);
return x_70;
}
}
else
{
lean_object* x_75; 
lean_dec(x_2);
x_75 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_62);
lean_ctor_set(x_78, 1, x_63);
lean_ctor_set(x_78, 2, x_76);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_dec(x_63);
lean_dec(x_62);
return x_75;
}
}
}
case 1:
{
uint8_t x_80; 
lean_inc_ref(x_64);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_2);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_2, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_2, 0);
lean_dec(x_83);
x_84 = lean_int_add(x_59, x_62);
lean_dec(x_62);
lean_dec(x_59);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
x_88 = lean_int_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_61, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_ctor_set(x_2, 2, x_91);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_86);
lean_ctor_set(x_89, 0, x_2);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
lean_ctor_set(x_2, 2, x_92);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_86);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_2);
return x_93;
}
}
else
{
lean_dec(x_86);
lean_free_object(x_2);
lean_dec(x_60);
return x_89;
}
}
else
{
lean_dec(x_86);
lean_free_object(x_2);
lean_dec(x_60);
x_1 = x_61;
x_2 = x_64;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_free_object(x_2);
lean_dec_ref(x_64);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_12);
x_95 = !lean_is_exclusive(x_85);
if (x_95 == 0)
{
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_85, 0);
lean_inc(x_96);
lean_dec(x_85);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
x_98 = lean_int_add(x_59, x_62);
lean_dec(x_62);
lean_dec(x_59);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
x_102 = lean_int_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_61, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_60);
lean_ctor_set(x_106, 2, x_104);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_dec(x_100);
lean_dec(x_60);
return x_103;
}
}
else
{
lean_dec(x_100);
lean_dec(x_60);
x_1 = x_61;
x_2 = x_64;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec_ref(x_64);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_12);
x_109 = lean_ctor_get(x_99, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_110 = x_99;
} else {
 lean_dec_ref(x_99);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
return x_111;
}
}
}
default: 
{
uint8_t x_112; 
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_112 = !lean_is_exclusive(x_1);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_1, 2);
lean_dec(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_dec(x_114);
x_115 = lean_ctor_get(x_1, 0);
lean_dec(x_115);
x_116 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 0);
lean_ctor_set(x_1, 2, x_118);
lean_ctor_set(x_116, 0, x_1);
return x_116;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
lean_ctor_set(x_1, 2, x_119);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_1);
return x_120;
}
}
else
{
lean_free_object(x_1);
lean_dec(x_60);
lean_dec(x_59);
return x_116;
}
}
else
{
lean_object* x_121; 
lean_dec(x_1);
x_121 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_59);
lean_ctor_set(x_124, 1, x_60);
lean_ctor_set(x_124, 2, x_122);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
else
{
lean_dec(x_60);
lean_dec(x_59);
return x_121;
}
}
}
}
}
}
}
else
{
lean_object* x_126; 
lean_free_object(x_12);
lean_dec_ref(x_29);
lean_dec(x_28);
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_126 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_21);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; uint8_t x_143; 
x_127 = lean_ctor_get(x_12, 0);
x_128 = lean_ctor_get(x_12, 1);
x_129 = lean_ctor_get(x_12, 2);
x_130 = lean_ctor_get(x_12, 3);
x_131 = lean_ctor_get(x_12, 4);
x_132 = lean_ctor_get(x_12, 5);
x_133 = lean_ctor_get(x_12, 6);
x_134 = lean_ctor_get(x_12, 7);
x_135 = lean_ctor_get(x_12, 8);
x_136 = lean_ctor_get(x_12, 9);
x_137 = lean_ctor_get(x_12, 10);
x_138 = lean_ctor_get(x_12, 11);
x_139 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_140 = lean_ctor_get(x_12, 12);
x_141 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_142 = lean_ctor_get(x_12, 13);
lean_inc(x_142);
lean_inc(x_140);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_12);
x_143 = lean_nat_dec_eq(x_130, x_131);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_130, x_144);
lean_dec(x_130);
x_146 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_146, 0, x_127);
lean_ctor_set(x_146, 1, x_128);
lean_ctor_set(x_146, 2, x_129);
lean_ctor_set(x_146, 3, x_145);
lean_ctor_set(x_146, 4, x_131);
lean_ctor_set(x_146, 5, x_132);
lean_ctor_set(x_146, 6, x_133);
lean_ctor_set(x_146, 7, x_134);
lean_ctor_set(x_146, 8, x_135);
lean_ctor_set(x_146, 9, x_136);
lean_ctor_set(x_146, 10, x_137);
lean_ctor_set(x_146, 11, x_138);
lean_ctor_set(x_146, 12, x_140);
lean_ctor_set(x_146, 13, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*14, x_139);
lean_ctor_set_uint8(x_146, sizeof(void*)*14 + 1, x_141);
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_149 = x_2;
} else {
 lean_dec_ref(x_2);
 x_149 = lean_box(0);
}
x_150 = lean_int_add(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
x_151 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
lean_dec_ref(x_146);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(0, 1, 0);
} else {
 x_154 = x_149;
}
lean_ctor_set(x_154, 0, x_152);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 1, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_149);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
lean_dec_ref(x_1);
x_160 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_2, x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
lean_dec_ref(x_146);
lean_dec(x_159);
return x_160;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_2, 0);
lean_inc(x_161);
lean_dec_ref(x_2);
x_162 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(x_1, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
lean_dec_ref(x_146);
lean_dec(x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_163 = lean_ctor_get(x_1, 0);
x_164 = lean_ctor_get(x_1, 1);
x_165 = lean_ctor_get(x_1, 2);
x_166 = lean_ctor_get(x_2, 0);
x_167 = lean_ctor_get(x_2, 1);
x_168 = lean_ctor_get(x_2, 2);
x_169 = l_Lean_Grind_CommRing_Mon_grevlex(x_164, x_167);
switch (x_169) {
case 0:
{
lean_object* x_170; lean_object* x_171; 
lean_inc_ref(x_168);
lean_inc(x_167);
lean_inc(x_166);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_170 = x_2;
} else {
 lean_dec_ref(x_2);
 x_170 = lean_box(0);
}
x_171 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_1, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_174 = lean_alloc_ctor(1, 3, 0);
} else {
 x_174 = x_170;
}
lean_ctor_set(x_174, 0, x_166);
lean_ctor_set(x_174, 1, x_167);
lean_ctor_set(x_174, 2, x_172);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 1, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
else
{
lean_dec(x_170);
lean_dec(x_167);
lean_dec(x_166);
return x_171;
}
}
case 1:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_inc_ref(x_168);
lean_inc(x_166);
lean_inc_ref(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_176 = x_2;
} else {
 lean_dec_ref(x_2);
 x_176 = lean_box(0);
}
x_177 = lean_int_add(x_163, x_166);
lean_dec(x_166);
lean_dec(x_163);
x_178 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_177, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
x_181 = lean_int_dec_eq(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_165, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_185 = lean_alloc_ctor(1, 3, 0);
} else {
 x_185 = x_176;
}
lean_ctor_set(x_185, 0, x_179);
lean_ctor_set(x_185, 1, x_164);
lean_ctor_set(x_185, 2, x_183);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 1, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
else
{
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_164);
return x_182;
}
}
else
{
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_164);
x_1 = x_165;
x_2 = x_168;
x_12 = x_146;
goto _start;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_176);
lean_dec_ref(x_168);
lean_dec_ref(x_165);
lean_dec(x_164);
lean_dec_ref(x_146);
x_188 = lean_ctor_get(x_178, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_189 = x_178;
} else {
 lean_dec_ref(x_178);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_188);
return x_190;
}
}
default: 
{
lean_object* x_191; lean_object* x_192; 
lean_inc_ref(x_165);
lean_inc(x_164);
lean_inc(x_163);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_191 = x_1;
} else {
 lean_dec_ref(x_1);
 x_191 = lean_box(0);
}
x_192 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_165, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146, x_13);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(1, 3, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_163);
lean_ctor_set(x_195, 1, x_164);
lean_ctor_set(x_195, 2, x_193);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 1, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
else
{
lean_dec(x_191);
lean_dec(x_164);
lean_dec(x_163);
return x_192;
}
}
}
}
}
}
else
{
lean_object* x_197; 
lean_dec_ref(x_142);
lean_dec(x_140);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_197 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_132);
return x_197;
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
x_23 = lean_ctor_get(x_13, 6);
x_24 = lean_ctor_get(x_13, 7);
x_25 = lean_ctor_get(x_13, 8);
x_26 = lean_ctor_get(x_13, 9);
x_27 = lean_ctor_get(x_13, 10);
x_28 = lean_ctor_get(x_13, 11);
x_29 = lean_ctor_get(x_13, 12);
x_30 = lean_ctor_get(x_13, 13);
x_31 = lean_nat_dec_eq(x_20, x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_20, x_32);
lean_dec(x_20);
lean_ctor_set(x_13, 3, x_33);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec_ref(x_2);
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_34, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_3, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
else
{
lean_dec_ref(x_13);
lean_dec_ref(x_3);
return x_35;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_40);
lean_dec_ref(x_2);
x_41 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
x_42 = l_Lean_Core_checkSystem(x_41, x_13, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec_ref(x_42);
lean_inc_ref(x_1);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_38, x_39, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
lean_inc_ref(x_13);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_3, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_2 = x_40;
x_3 = x_46;
goto _start;
}
else
{
lean_dec_ref(x_40);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
return x_45;
}
}
else
{
lean_dec_ref(x_40);
lean_dec_ref(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_43;
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
lean_free_object(x_13);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_22);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
x_54 = lean_ctor_get(x_13, 2);
x_55 = lean_ctor_get(x_13, 3);
x_56 = lean_ctor_get(x_13, 4);
x_57 = lean_ctor_get(x_13, 5);
x_58 = lean_ctor_get(x_13, 6);
x_59 = lean_ctor_get(x_13, 7);
x_60 = lean_ctor_get(x_13, 8);
x_61 = lean_ctor_get(x_13, 9);
x_62 = lean_ctor_get(x_13, 10);
x_63 = lean_ctor_get(x_13, 11);
x_64 = lean_ctor_get_uint8(x_13, sizeof(void*)*14);
x_65 = lean_ctor_get(x_13, 12);
x_66 = lean_ctor_get_uint8(x_13, sizeof(void*)*14 + 1);
x_67 = lean_ctor_get(x_13, 13);
lean_inc(x_67);
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_68 = lean_nat_dec_eq(x_55, x_56);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_55, x_69);
lean_dec(x_55);
x_71 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
lean_ctor_set(x_71, 2, x_54);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_56);
lean_ctor_set(x_71, 5, x_57);
lean_ctor_set(x_71, 6, x_58);
lean_ctor_set(x_71, 7, x_59);
lean_ctor_set(x_71, 8, x_60);
lean_ctor_set(x_71, 9, x_61);
lean_ctor_set(x_71, 10, x_62);
lean_ctor_set(x_71, 11, x_63);
lean_ctor_set(x_71, 12, x_65);
lean_ctor_set(x_71, 13, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*14, x_64);
lean_ctor_set_uint8(x_71, sizeof(void*)*14 + 1, x_66);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec_ref(x_2);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_72, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_71, x_14);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_3, x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_71, x_14);
return x_75;
}
else
{
lean_dec_ref(x_71);
lean_dec_ref(x_3);
return x_73;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_78);
lean_dec_ref(x_2);
x_79 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0));
x_80 = l_Lean_Core_checkSystem(x_79, x_71, x_14);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec_ref(x_80);
lean_inc_ref(x_1);
x_81 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_76, x_77, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_71, x_14);
lean_dec(x_76);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc_ref(x_71);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_3, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_71, x_14);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_2 = x_78;
x_3 = x_84;
x_13 = x_71;
goto _start;
}
else
{
lean_dec_ref(x_78);
lean_dec_ref(x_71);
lean_dec_ref(x_1);
return x_83;
}
}
else
{
lean_dec_ref(x_78);
lean_dec_ref(x_71);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_81;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_71);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_87 = x_80;
} else {
 lean_dec_ref(x_80);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec_ref(x_67);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_57);
return x_89;
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_19 = lean_ctor_get(x_12, 3);
x_20 = lean_ctor_get(x_12, 4);
x_21 = lean_ctor_get(x_12, 5);
x_22 = lean_ctor_get(x_12, 6);
x_23 = lean_ctor_get(x_12, 7);
x_24 = lean_ctor_get(x_12, 8);
x_25 = lean_ctor_get(x_12, 9);
x_26 = lean_ctor_get(x_12, 10);
x_27 = lean_ctor_get(x_12, 11);
x_28 = lean_ctor_get(x_12, 12);
x_29 = lean_ctor_get(x_12, 13);
x_30 = lean_nat_dec_eq(x_19, x_20);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_2, x_31);
if (x_32 == 1)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_12);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_1);
x_33 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_2, x_35);
x_37 = lean_nat_dec_eq(x_36, x_31);
if (x_37 == 1)
{
lean_object* x_38; 
lean_dec(x_36);
lean_free_object(x_12);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_nat_sub(x_36, x_35);
lean_dec(x_36);
x_40 = lean_nat_add(x_19, x_35);
lean_dec(x_19);
lean_ctor_set(x_12, 3, x_40);
x_41 = lean_nat_dec_eq(x_39, x_31);
if (x_41 == 1)
{
lean_object* x_42; 
lean_dec(x_39);
lean_inc_ref(x_1);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_nat_sub(x_39, x_35);
lean_dec(x_39);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_43);
lean_inc_ref(x_12);
lean_inc_ref(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_1, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_48;
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_1);
return x_46;
}
}
}
}
}
else
{
lean_object* x_49; 
lean_free_object(x_12);
lean_dec_ref(x_29);
lean_dec(x_28);
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
lean_dec_ref(x_1);
x_49 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_21);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
x_52 = lean_ctor_get(x_12, 2);
x_53 = lean_ctor_get(x_12, 3);
x_54 = lean_ctor_get(x_12, 4);
x_55 = lean_ctor_get(x_12, 5);
x_56 = lean_ctor_get(x_12, 6);
x_57 = lean_ctor_get(x_12, 7);
x_58 = lean_ctor_get(x_12, 8);
x_59 = lean_ctor_get(x_12, 9);
x_60 = lean_ctor_get(x_12, 10);
x_61 = lean_ctor_get(x_12, 11);
x_62 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_63 = lean_ctor_get(x_12, 12);
x_64 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_65 = lean_ctor_get(x_12, 13);
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_66 = lean_nat_dec_eq(x_53, x_54);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_eq(x_2, x_67);
if (x_68 == 1)
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_65);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_1);
x_69 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_2, x_71);
x_73 = lean_nat_dec_eq(x_72, x_67);
if (x_73 == 1)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec_ref(x_65);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_1);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_nat_sub(x_72, x_71);
lean_dec(x_72);
x_76 = lean_nat_add(x_53, x_71);
lean_dec(x_53);
x_77 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_77, 0, x_50);
lean_ctor_set(x_77, 1, x_51);
lean_ctor_set(x_77, 2, x_52);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 4, x_54);
lean_ctor_set(x_77, 5, x_55);
lean_ctor_set(x_77, 6, x_56);
lean_ctor_set(x_77, 7, x_57);
lean_ctor_set(x_77, 8, x_58);
lean_ctor_set(x_77, 9, x_59);
lean_ctor_set(x_77, 10, x_60);
lean_ctor_set(x_77, 11, x_61);
lean_ctor_set(x_77, 12, x_63);
lean_ctor_set(x_77, 13, x_65);
lean_ctor_set_uint8(x_77, sizeof(void*)*14, x_62);
lean_ctor_set_uint8(x_77, sizeof(void*)*14 + 1, x_64);
x_78 = lean_nat_dec_eq(x_75, x_67);
if (x_78 == 1)
{
lean_object* x_79; 
lean_dec(x_75);
lean_inc_ref(x_1);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77, x_13);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_nat_sub(x_75, x_71);
lean_dec(x_75);
x_81 = lean_unsigned_to_nat(2u);
x_82 = lean_nat_add(x_80, x_81);
lean_dec(x_80);
lean_inc_ref(x_77);
lean_inc_ref(x_1);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_1, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77, x_13);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_1, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77, x_13);
return x_85;
}
else
{
lean_dec_ref(x_77);
lean_dec_ref(x_1);
return x_83;
}
}
}
}
}
else
{
lean_object* x_86; 
lean_dec_ref(x_65);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_1);
x_86 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(x_55);
return x_86;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_nat_to_int(x_41);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_45);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_1);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_nat_to_int(x_53);
x_55 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
}
case 3:
{
uint8_t x_64; 
lean_dec_ref(x_11);
x_64 = !lean_is_exclusive(x_1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_1, 0);
x_66 = l_Lean_Grind_CommRing_Poly_ofVar(x_65);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_66);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_1);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = l_Lean_Grind_CommRing_Poly_ofVar(x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
case 4:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_72);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_11);
return x_73;
}
else
{
uint8_t x_75; 
lean_dec_ref(x_73);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_77, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_ctor_set(x_74, 0, x_80);
lean_ctor_set(x_78, 0, x_74);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
lean_ctor_set(x_74, 0, x_81);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_74);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_74);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
lean_dec(x_74);
x_87 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
x_88 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_87, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_94 = x_88;
} else {
 lean_dec_ref(x_88);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
}
}
else
{
lean_dec_ref(x_11);
return x_73;
}
}
case 5:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_97);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_98 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_dec_ref(x_97);
lean_dec_ref(x_11);
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
lean_inc_ref(x_11);
x_101 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_dec(x_100);
lean_dec_ref(x_11);
return x_101;
}
else
{
uint8_t x_103; 
lean_dec_ref(x_101);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_100, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_ctor_set(x_102, 0, x_107);
lean_ctor_set(x_105, 0, x_102);
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
lean_ctor_set(x_102, 0, x_108);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_102);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_free_object(x_102);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_105, 0);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_102, 0);
lean_inc(x_113);
lean_dec(x_102);
x_114 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_100, x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_115);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 1, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_120 = x_114;
} else {
 lean_dec_ref(x_114);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
}
}
else
{
lean_dec(x_100);
lean_dec_ref(x_11);
return x_101;
}
}
}
else
{
lean_dec_ref(x_97);
lean_dec_ref(x_11);
return x_98;
}
}
case 6:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_123);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_123);
lean_dec_ref(x_11);
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
lean_inc_ref(x_11);
x_127 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_126);
lean_dec_ref(x_11);
return x_127;
}
else
{
uint8_t x_129; 
lean_dec_ref(x_127);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
x_132 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_131, x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_126, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_ctor_set(x_128, 0, x_136);
lean_ctor_set(x_134, 0, x_128);
return x_134;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
lean_ctor_set(x_128, 0, x_137);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_128);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_free_object(x_128);
x_139 = !lean_is_exclusive(x_134);
if (x_139 == 0)
{
return x_134;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_free_object(x_128);
lean_dec(x_126);
lean_dec_ref(x_11);
x_142 = !lean_is_exclusive(x_132);
if (x_142 == 0)
{
return x_132;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_132, 0);
lean_inc(x_143);
lean_dec(x_132);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_128, 0);
lean_inc(x_145);
lean_dec(x_128);
x_146 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(x_146, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_126, x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_150);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_155 = x_149;
} else {
 lean_dec_ref(x_149);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_126);
lean_dec_ref(x_11);
x_157 = lean_ctor_get(x_147, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_158 = x_147;
} else {
 lean_dec_ref(x_147);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
}
}
else
{
lean_dec(x_126);
lean_dec_ref(x_11);
return x_127;
}
}
}
else
{
lean_dec_ref(x_123);
lean_dec_ref(x_11);
return x_124;
}
}
case 7:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_161);
lean_dec_ref(x_1);
lean_inc_ref(x_11);
x_162 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_160, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_161);
lean_dec_ref(x_11);
return x_162;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
lean_inc_ref(x_11);
x_165 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec(x_164);
lean_dec_ref(x_11);
return x_165;
}
else
{
uint8_t x_167; 
lean_dec_ref(x_165);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_164, x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_169, 0);
lean_ctor_set(x_166, 0, x_171);
lean_ctor_set(x_169, 0, x_166);
return x_169;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
lean_dec(x_169);
lean_ctor_set(x_166, 0, x_172);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_166);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_free_object(x_166);
x_174 = !lean_is_exclusive(x_169);
if (x_174 == 0)
{
return x_169;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_166, 0);
lean_inc(x_177);
lean_dec(x_166);
x_178 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(x_164, x_177, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_179);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 1, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_178, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_184 = x_178;
} else {
 lean_dec_ref(x_178);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
return x_185;
}
}
}
}
else
{
lean_dec(x_164);
lean_dec_ref(x_11);
return x_165;
}
}
}
else
{
lean_dec_ref(x_161);
lean_dec_ref(x_11);
return x_162;
}
}
case 8:
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_1);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_1, 0);
x_188 = lean_ctor_get(x_1, 1);
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_nat_dec_eq(x_188, x_189);
if (x_190 == 0)
{
switch (lean_obj_tag(x_187)) {
case 0:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_1);
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
lean_inc(x_188);
x_193 = l_Lean_Meta_Grind_Arith_checkExp(x_188, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_193) == 0)
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
if (lean_obj_tag(x_195) == 0)
{
if (x_190 == 0)
{
lean_object* x_210; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_188);
lean_dec_ref(x_11);
x_210 = lean_box(0);
lean_ctor_set(x_193, 0, x_210);
return x_193;
}
else
{
lean_free_object(x_193);
goto block_209;
}
}
else
{
lean_dec_ref(x_195);
lean_free_object(x_193);
goto block_209;
}
block_209:
{
lean_object* x_196; lean_object* x_197; 
x_196 = l_Int_pow(x_191, x_188);
lean_dec(x_188);
lean_dec(x_191);
x_197 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_196, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_197, 0);
if (lean_is_scalar(x_192)) {
 x_200 = lean_alloc_ctor(0, 1, 0);
} else {
 x_200 = x_192;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_197, 0, x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_197, 0);
lean_inc(x_202);
lean_dec(x_197);
if (lean_is_scalar(x_192)) {
 x_203 = lean_alloc_ctor(0, 1, 0);
} else {
 x_203 = x_192;
}
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_192);
x_206 = !lean_is_exclusive(x_197);
if (x_206 == 0)
{
return x_197;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_197, 0);
lean_inc(x_207);
lean_dec(x_197);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
}
}
}
else
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_193, 0);
lean_inc(x_211);
lean_dec(x_193);
if (lean_obj_tag(x_211) == 0)
{
if (x_190 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_188);
lean_dec_ref(x_11);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
else
{
goto block_222;
}
}
else
{
lean_dec_ref(x_211);
goto block_222;
}
block_222:
{
lean_object* x_212; lean_object* x_213; 
x_212 = l_Int_pow(x_191, x_188);
lean_dec(x_188);
lean_dec(x_191);
x_213 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_212, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_215 = x_213;
} else {
 lean_dec_ref(x_213);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_192;
}
lean_ctor_set(x_216, 0, x_214);
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_216);
if (lean_is_scalar(x_215)) {
 x_218 = lean_alloc_ctor(0, 1, 0);
} else {
 x_218 = x_215;
}
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_192);
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_220 = x_213;
} else {
 lean_dec_ref(x_213);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
return x_221;
}
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_188);
lean_dec_ref(x_11);
x_225 = !lean_is_exclusive(x_193);
if (x_225 == 0)
{
return x_193;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_193, 0);
lean_inc(x_226);
lean_dec(x_193);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
case 3:
{
uint8_t x_228; 
lean_dec_ref(x_11);
x_228 = !lean_is_exclusive(x_187);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_187, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_229);
x_230 = lean_box(0);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_1);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Grind_CommRing_Poly_ofMon(x_231);
lean_ctor_set_tag(x_187, 1);
lean_ctor_set(x_187, 0, x_232);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_187);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_187, 0);
lean_inc(x_234);
lean_dec(x_187);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_234);
x_235 = lean_box(0);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_1);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Grind_CommRing_Poly_ofMon(x_236);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
default: 
{
lean_object* x_240; 
lean_free_object(x_1);
lean_inc_ref(x_11);
x_240 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_dec(x_188);
lean_dec_ref(x_11);
return x_240;
}
else
{
uint8_t x_242; 
lean_dec_ref(x_240);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_241, 0);
x_244 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_243, x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_188);
if (lean_obj_tag(x_244) == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_244, 0);
lean_ctor_set(x_241, 0, x_246);
lean_ctor_set(x_244, 0, x_241);
return x_244;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
lean_dec(x_244);
lean_ctor_set(x_241, 0, x_247);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_241);
return x_248;
}
}
else
{
uint8_t x_249; 
lean_free_object(x_241);
x_249 = !lean_is_exclusive(x_244);
if (x_249 == 0)
{
return x_244;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_244, 0);
lean_inc(x_250);
lean_dec(x_244);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_241, 0);
lean_inc(x_252);
lean_dec(x_241);
x_253 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_252, x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_188);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_254);
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(0, 1, 0);
} else {
 x_257 = x_255;
}
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_253, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
}
}
}
else
{
lean_dec(x_188);
lean_dec_ref(x_11);
return x_240;
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_free_object(x_1);
lean_dec(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_11);
x_261 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_261);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_1, 0);
x_264 = lean_ctor_get(x_1, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_1);
x_265 = lean_unsigned_to_nat(0u);
x_266 = lean_nat_dec_eq(x_264, x_265);
if (x_266 == 0)
{
switch (lean_obj_tag(x_263)) {
case 0:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_268 = x_263;
} else {
 lean_dec_ref(x_263);
 x_268 = lean_box(0);
}
lean_inc(x_264);
x_269 = l_Lean_Meta_Grind_Arith_checkExp(x_264, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
if (lean_obj_tag(x_270) == 0)
{
if (x_266 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_264);
lean_dec_ref(x_11);
x_283 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_284 = lean_alloc_ctor(0, 1, 0);
} else {
 x_284 = x_271;
}
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
else
{
lean_dec(x_271);
goto block_282;
}
}
else
{
lean_dec_ref(x_270);
lean_dec(x_271);
goto block_282;
}
block_282:
{
lean_object* x_272; lean_object* x_273; 
x_272 = l_Int_pow(x_267, x_264);
lean_dec(x_264);
lean_dec(x_267);
x_273 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_272, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_275 = x_273;
} else {
 lean_dec_ref(x_273);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_268;
}
lean_ctor_set(x_276, 0, x_274);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
if (lean_is_scalar(x_275)) {
 x_278 = lean_alloc_ctor(0, 1, 0);
} else {
 x_278 = x_275;
}
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_268);
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_264);
lean_dec_ref(x_11);
x_285 = lean_ctor_get(x_269, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_286 = x_269;
} else {
 lean_dec_ref(x_269);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 1, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_285);
return x_287;
}
}
case 3:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_11);
x_288 = lean_ctor_get(x_263, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_289 = x_263;
} else {
 lean_dec_ref(x_263);
 x_289 = lean_box(0);
}
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_264);
x_291 = lean_box(0);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_Grind_CommRing_Poly_ofMon(x_292);
if (lean_is_scalar(x_289)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_289;
 lean_ctor_set_tag(x_294, 1);
}
lean_ctor_set(x_294, 0, x_293);
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_294);
return x_295;
}
default: 
{
lean_object* x_296; 
lean_inc_ref(x_11);
x_296 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_263, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_dec(x_264);
lean_dec_ref(x_11);
return x_296;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec_ref(x_296);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
x_300 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(x_298, x_264, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_264);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_303 = lean_alloc_ctor(1, 1, 0);
} else {
 x_303 = x_299;
}
lean_ctor_set(x_303, 0, x_301);
if (lean_is_scalar(x_302)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_302;
}
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_299);
x_305 = lean_ctor_get(x_300, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_306 = x_300;
} else {
 lean_dec_ref(x_300);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
return x_307;
}
}
}
else
{
lean_dec(x_264);
lean_dec_ref(x_11);
return x_296;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_11);
x_308 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
x_309 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
}
}
default: 
{
lean_object* x_310; 
x_310 = lean_ctor_get(x_1, 0);
lean_inc(x_310);
lean_dec_ref(x_1);
x_14 = x_310;
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
x_26 = lean_box(0);
goto block_39;
}
}
block_39:
{
lean_object* x_27; 
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
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
lean_object* x_15; 
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_24);
lean_dec_ref(x_2);
lean_inc(x_23);
lean_inc(x_20);
x_25 = l_Lean_Grind_CommRing_Mon_lcm(x_20, x_23);
lean_inc(x_25);
x_26 = l_Lean_Grind_CommRing_Mon_div(x_25, x_20);
x_27 = lean_nat_abs(x_19);
x_28 = lean_nat_abs(x_22);
x_29 = lean_nat_gcd(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_int_ediv(x_22, x_30);
lean_dec(x_22);
lean_inc(x_26);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_31, x_26, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Grind_CommRing_Mon_div(x_25, x_23);
x_35 = lean_int_neg(x_19);
lean_dec(x_19);
x_36 = lean_int_ediv(x_35, x_30);
lean_dec(x_30);
lean_dec(x_35);
lean_inc(x_34);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(x_36, x_34, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(x_33, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_34);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_26);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec_ref(x_12);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec_ref(x_12);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_12);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spolM___closed__0, &l_Lean_Grind_CommRing_Poly_spolM___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
x_74 = lean_ctor_get(x_21, 2);
x_75 = l_Lean_instInhabitedExpr;
x_76 = lean_nat_dec_lt(x_22, x_74);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec_ref(x_21);
x_77 = l_outOfBounds___redArg(x_75);
x_24 = x_77;
goto block_73;
}
else
{
lean_object* x_78; 
x_78 = l_Lean_PersistentArray_get_x21___redArg(x_75, x_21, x_22);
x_24 = x_78;
goto block_73;
}
block_73:
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_cleanupAnnotations(x_24);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_28);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_36 = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2));
x_37 = l_Lean_Expr_isConstOf(x_35, x_36);
lean_dec_ref(x_35);
if (x_37 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Expr_cleanupAnnotations(x_28);
x_40 = l_Lean_Expr_isApp(x_39);
if (x_40 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Expr_appFnCleanup___redArg(x_39);
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_dec_ref(x_42);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_45);
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = ((lean_object*)(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5));
x_51 = l_Lean_Expr_isConstOf(x_49, x_50);
lean_dec_ref(x_49);
if (x_51 == 0)
{
lean_dec_ref(x_45);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
else
{
lean_object* x_53; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_53 = l_Lean_Meta_getNatValue_x3f(x_45, x_9, x_10, x_11, x_12);
lean_dec_ref(x_45);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
if (lean_obj_tag(x_55) == 1)
{
uint8_t x_56; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
if (lean_is_scalar(x_23)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_23;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_22);
lean_ctor_set(x_55, 0, x_58);
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
if (lean_is_scalar(x_23)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_23;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_53, 0, x_61);
return x_53;
}
}
else
{
lean_free_object(x_53);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec(x_53);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_23;
}
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_22);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_dec(x_63);
lean_dec(x_23);
lean_dec(x_22);
x_1 = x_17;
goto _start;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_70 = !lean_is_exclusive(x_53);
if (x_70 == 0)
{
return x_53;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_53, 0);
lean_inc(x_71);
lean_dec(x_53);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
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
uint8_t x_79; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_79 = !lean_is_exclusive(x_18);
if (x_79 == 0)
{
return x_18;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_18, 0);
lean_inc(x_80);
lean_dec(x_18);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
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
uint8_t x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_21 = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 1)
{
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_21;
}
else
{
lean_dec_ref(x_21);
lean_dec(x_22);
x_1 = x_20;
goto _start;
}
}
else
{
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_21;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
