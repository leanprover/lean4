// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Init.Grind.Propagator import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing import Lean.Meta.NatInstTesters public import Lean.Meta.Tactic.Grind.PropagatorAttr import Init.Data.Nat.Dvd
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
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 149, 0, 200, 120, 117, 225, 20)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(236, 213, 16, 64, 1, 14, 244, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 38, 232, 206, 222, 75, 121, 224)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 174, 99, 3, 215, 140, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(57, 234, 237, 24, 129, 31, 246, 138)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "non-linear divisibility constraint found"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "emod_pos_of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(38, 146, 134, 59, 191, 125, 100, 172)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "of_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 103, 37, 221, 182, 135, 125, 134)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
x_33 = l_Int_Linear_Poly_isSorted(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_32);
x_34 = l_Int_Linear_Poly_norm(x_32);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_1);
lean_inc_ref(x_34);
lean_inc(x_31);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_23 = x_36;
x_24 = x_31;
x_25 = x_34;
goto block_30;
}
else
{
lean_inc_ref(x_32);
x_23 = x_1;
x_24 = x_31;
x_25 = x_32;
goto block_30;
}
block_11:
{
if (x_6 == 0)
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_4, x_3);
lean_dec(x_4);
x_8 = l_Int_Linear_Poly_div(x_3, x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Int_Linear_Poly_getConst(x_15);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_13);
lean_dec(x_13);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_12;
x_3 = x_16;
x_4 = x_14;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
x_21 = lean_int_dec_eq(x_16, x_20);
if (x_21 == 0)
{
x_2 = x_12;
x_3 = x_16;
x_4 = x_14;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
return x_12;
}
}
}
block_30:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_24);
x_26 = l_Int_Linear_Poly_gcdCoeffs(x_25, x_24);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
x_28 = lean_int_dec_lt(x_24, x_27);
if (x_28 == 0)
{
x_12 = x_23;
x_13 = x_27;
x_14 = x_24;
x_15 = x_25;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_23;
x_13 = x_27;
x_14 = x_24;
x_15 = x_25;
x_16 = x_29;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_36; 
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
x_18 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_17, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_int_mul(x_1, x_22);
x_25 = lean_nat_abs(x_24);
lean_dec(x_24);
x_26 = lean_nat_to_int(x_25);
lean_inc_ref(x_23);
x_27 = l_Int_Linear_Poly_mul(x_23, x_1);
x_28 = lean_int_neg(x_4);
lean_inc_ref(x_21);
x_29 = l_Int_Linear_Poly_mul(x_21, x_28);
lean_dec(x_28);
x_30 = l_Int_Linear_Poly_combine(x_27, x_29);
x_36 = lean_unbox(x_19);
lean_dec(x_19);
if (x_36 == 0)
{
x_31 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_3);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc_ref(x_5);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_14);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_MessageData_ofExpr(x_38);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
x_49 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_17, x_48, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_49);
x_31 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_50; 
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_41);
if (x_53 == 0)
{
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_38);
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
return x_39;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_39, 0);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_37);
if (x_59 == 0)
{
return x_37;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_37, 0);
lean_inc(x_60);
lean_dec(x_37);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
block_35:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_5);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
if (lean_is_scalar(x_20)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_20;
}
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_14;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
x_18 = lean_ctor_get(x_10, 4);
x_19 = lean_ctor_get(x_10, 5);
x_20 = lean_ctor_get(x_10, 6);
x_21 = lean_ctor_get(x_10, 7);
x_22 = lean_ctor_get(x_10, 8);
x_23 = lean_ctor_get(x_10, 9);
x_24 = lean_ctor_get(x_10, 10);
x_25 = lean_ctor_get(x_10, 11);
x_26 = lean_ctor_get(x_10, 12);
x_27 = lean_ctor_get(x_10, 13);
x_28 = lean_nat_dec_eq(x_17, x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_17, x_30);
lean_dec(x_17);
lean_ctor_set(x_10, 3, x_31);
lean_inc_ref(x_29);
x_32 = l_Int_Linear_Poly_findVarToSubst___redArg(x_29, x_2, x_10);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_37, 0);
x_41 = l_Int_Linear_Poly_coeff(x_40, x_39);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_41, x_39, x_37, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_38);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_1 = x_43;
goto _start;
}
else
{
lean_dec_ref(x_10);
return x_42;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_10);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 0);
x_52 = l_Int_Linear_Poly_coeff(x_51, x_50);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_52, x_50, x_48, x_49, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_49);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_1 = x_54;
goto _start;
}
else
{
lean_dec_ref(x_10);
return x_53;
}
}
else
{
lean_object* x_56; 
lean_dec(x_45);
lean_dec_ref(x_10);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_1);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_32);
if (x_57 == 0)
{
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_free_object(x_10);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_60 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_19);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_61 = lean_ctor_get(x_10, 0);
x_62 = lean_ctor_get(x_10, 1);
x_63 = lean_ctor_get(x_10, 2);
x_64 = lean_ctor_get(x_10, 3);
x_65 = lean_ctor_get(x_10, 4);
x_66 = lean_ctor_get(x_10, 5);
x_67 = lean_ctor_get(x_10, 6);
x_68 = lean_ctor_get(x_10, 7);
x_69 = lean_ctor_get(x_10, 8);
x_70 = lean_ctor_get(x_10, 9);
x_71 = lean_ctor_get(x_10, 10);
x_72 = lean_ctor_get(x_10, 11);
x_73 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_74 = lean_ctor_get(x_10, 12);
x_75 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_76 = lean_ctor_get(x_10, 13);
lean_inc(x_76);
lean_inc(x_74);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_10);
x_77 = lean_nat_dec_eq(x_64, x_65);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_1, 1);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_64, x_79);
lean_dec(x_64);
x_81 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_81, 0, x_61);
lean_ctor_set(x_81, 1, x_62);
lean_ctor_set(x_81, 2, x_63);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_81, 4, x_65);
lean_ctor_set(x_81, 5, x_66);
lean_ctor_set(x_81, 6, x_67);
lean_ctor_set(x_81, 7, x_68);
lean_ctor_set(x_81, 8, x_69);
lean_ctor_set(x_81, 9, x_70);
lean_ctor_set(x_81, 10, x_71);
lean_ctor_set(x_81, 11, x_72);
lean_ctor_set(x_81, 12, x_74);
lean_ctor_set(x_81, 13, x_76);
lean_ctor_set_uint8(x_81, sizeof(void*)*14, x_73);
lean_ctor_set_uint8(x_81, sizeof(void*)*14 + 1, x_75);
lean_inc_ref(x_78);
x_82 = l_Int_Linear_Poly_findVarToSubst___redArg(x_78, x_2, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_ctor_get(x_87, 0);
x_91 = l_Int_Linear_Poly_coeff(x_90, x_89);
x_92 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_91, x_89, x_87, x_88, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81, x_11);
lean_dec(x_88);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_1 = x_93;
x_10 = x_81;
goto _start;
}
else
{
lean_dec_ref(x_81);
return x_92;
}
}
else
{
lean_object* x_95; 
lean_dec(x_83);
lean_dec_ref(x_81);
if (lean_is_scalar(x_84)) {
 x_95 = lean_alloc_ctor(0, 1, 0);
} else {
 x_95 = x_84;
}
lean_ctor_set(x_95, 0, x_1);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_81);
lean_dec_ref(x_1);
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_97 = x_82;
} else {
 lean_dec_ref(x_82);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec_ref(x_76);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_1);
x_99 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_66);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 6);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentArray_set___redArg(x_4, x_1, x_5);
lean_ctor_set(x_2, 6, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*23);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*23 + 1);
x_31 = lean_ctor_get(x_2, 22);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_Lean_PersistentArray_set___redArg(x_13, x_1, x_32);
x_34 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_9);
lean_ctor_set(x_34, 3, x_10);
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 5, x_12);
lean_ctor_set(x_34, 6, x_33);
lean_ctor_set(x_34, 7, x_14);
lean_ctor_set(x_34, 8, x_15);
lean_ctor_set(x_34, 9, x_16);
lean_ctor_set(x_34, 10, x_17);
lean_ctor_set(x_34, 11, x_18);
lean_ctor_set(x_34, 12, x_19);
lean_ctor_set(x_34, 13, x_20);
lean_ctor_set(x_34, 14, x_21);
lean_ctor_set(x_34, 15, x_23);
lean_ctor_set(x_34, 16, x_24);
lean_ctor_set(x_34, 17, x_25);
lean_ctor_set(x_34, 18, x_26);
lean_ctor_set(x_34, 19, x_27);
lean_ctor_set(x_34, 20, x_28);
lean_ctor_set(x_34, 21, x_29);
lean_ctor_set(x_34, 22, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*23, x_22);
lean_ctor_set_uint8(x_34, sizeof(void*)*23 + 1, x_30);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 6);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_PersistentArray_set___redArg(x_5, x_2, x_6);
lean_ctor_set(x_3, 6, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 7);
x_16 = lean_ctor_get(x_3, 8);
x_17 = lean_ctor_get(x_3, 9);
x_18 = lean_ctor_get(x_3, 10);
x_19 = lean_ctor_get(x_3, 11);
x_20 = lean_ctor_get(x_3, 12);
x_21 = lean_ctor_get(x_3, 13);
x_22 = lean_ctor_get(x_3, 14);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*23);
x_24 = lean_ctor_get(x_3, 15);
x_25 = lean_ctor_get(x_3, 16);
x_26 = lean_ctor_get(x_3, 17);
x_27 = lean_ctor_get(x_3, 18);
x_28 = lean_ctor_get(x_3, 19);
x_29 = lean_ctor_get(x_3, 20);
x_30 = lean_ctor_get(x_3, 21);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*23 + 1);
x_32 = lean_ctor_get(x_3, 22);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = l_Lean_PersistentArray_set___redArg(x_14, x_2, x_33);
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_10);
lean_ctor_set(x_35, 3, x_11);
lean_ctor_set(x_35, 4, x_12);
lean_ctor_set(x_35, 5, x_13);
lean_ctor_set(x_35, 6, x_34);
lean_ctor_set(x_35, 7, x_15);
lean_ctor_set(x_35, 8, x_16);
lean_ctor_set(x_35, 9, x_17);
lean_ctor_set(x_35, 10, x_18);
lean_ctor_set(x_35, 11, x_19);
lean_ctor_set(x_35, 12, x_20);
lean_ctor_set(x_35, 13, x_21);
lean_ctor_set(x_35, 14, x_22);
lean_ctor_set(x_35, 15, x_24);
lean_ctor_set(x_35, 16, x_25);
lean_ctor_set(x_35, 17, x_26);
lean_ctor_set(x_35, 18, x_27);
lean_ctor_set(x_35, 19, x_28);
lean_ctor_set(x_35, 20, x_29);
lean_ctor_set(x_35, 21, x_30);
lean_ctor_set(x_35, 22, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_23);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_31);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_45; uint8_t x_49; 
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
x_52 = lean_ctor_get(x_10, 2);
x_53 = lean_ctor_get(x_10, 3);
x_54 = lean_ctor_get(x_10, 4);
x_55 = lean_ctor_get(x_10, 5);
x_56 = lean_ctor_get(x_10, 6);
x_57 = lean_ctor_get(x_10, 7);
x_58 = lean_ctor_get(x_10, 8);
x_59 = lean_ctor_get(x_10, 9);
x_60 = lean_ctor_get(x_10, 10);
x_61 = lean_ctor_get(x_10, 11);
x_62 = lean_ctor_get(x_10, 12);
x_63 = lean_ctor_get(x_10, 13);
x_64 = lean_nat_dec_eq(x_53, x_54);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_53, x_65);
lean_dec(x_53);
lean_ctor_set(x_10, 3, x_66);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_220; lean_object* x_221; 
lean_free_object(x_67);
x_220 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
x_221 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_220, x_10);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_317; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = lean_box(0);
x_317 = lean_unbox(x_222);
lean_dec(x_222);
if (x_317 == 0)
{
x_254 = x_2;
x_255 = x_3;
x_256 = x_4;
x_257 = x_5;
x_258 = x_6;
x_259 = x_7;
x_260 = x_8;
x_261 = x_9;
x_262 = x_10;
x_263 = x_11;
x_264 = lean_box(0);
goto block_316;
}
else
{
lean_object* x_318; 
lean_inc_ref(x_1);
x_318 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_10);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec_ref(x_318);
x_320 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_220, x_319, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_320) == 0)
{
lean_dec_ref(x_320);
x_254 = x_2;
x_255 = x_3;
x_256 = x_4;
x_257 = x_5;
x_258 = x_6;
x_259 = x_7;
x_260 = x_8;
x_261 = x_9;
x_262 = x_10;
x_263 = x_11;
x_264 = lean_box(0);
goto block_316;
}
else
{
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_320;
}
}
else
{
uint8_t x_321; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_321 = !lean_is_exclusive(x_318);
if (x_321 == 0)
{
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
return x_323;
}
}
}
block_253:
{
lean_object* x_243; 
x_243 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_232, x_240);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = lean_ctor_get(x_244, 6);
lean_inc_ref(x_245);
lean_dec(x_244);
x_246 = lean_ctor_get(x_245, 2);
x_247 = lean_nat_dec_lt(x_231, x_246);
if (x_247 == 0)
{
lean_object* x_248; 
lean_dec_ref(x_245);
x_248 = l_outOfBounds___redArg(x_223);
x_71 = x_240;
x_72 = x_224;
x_73 = lean_box(0);
x_74 = x_226;
x_75 = x_227;
x_76 = x_241;
x_77 = x_232;
x_78 = x_238;
x_79 = x_236;
x_80 = x_230;
x_81 = x_233;
x_82 = x_225;
x_83 = x_237;
x_84 = x_234;
x_85 = x_228;
x_86 = x_229;
x_87 = x_235;
x_88 = x_231;
x_89 = x_239;
x_90 = x_248;
goto block_219;
}
else
{
lean_object* x_249; 
x_249 = l_Lean_PersistentArray_get_x21___redArg(x_223, x_245, x_231);
x_71 = x_240;
x_72 = x_224;
x_73 = lean_box(0);
x_74 = x_226;
x_75 = x_227;
x_76 = x_241;
x_77 = x_232;
x_78 = x_238;
x_79 = x_236;
x_80 = x_230;
x_81 = x_233;
x_82 = x_225;
x_83 = x_237;
x_84 = x_234;
x_85 = x_228;
x_86 = x_229;
x_87 = x_235;
x_88 = x_231;
x_89 = x_239;
x_90 = x_249;
goto block_219;
}
}
else
{
uint8_t x_250; 
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
x_250 = !lean_is_exclusive(x_243);
if (x_250 == 0)
{
return x_243;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_243, 0);
lean_inc(x_251);
lean_dec(x_243);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
return x_252;
}
}
}
block_316:
{
lean_object* x_265; lean_object* x_266; 
x_265 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_262);
x_266 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_265, x_254, x_255, x_256, x_257, x_258, x_259, x_260, x_261, x_262, x_263);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_ctor_get(x_267, 0);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
x_270 = l_Int_Linear_Poly_isUnsatDvd(x_268, x_269);
if (x_270 == 0)
{
uint8_t x_271; 
x_271 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_267);
if (x_271 == 0)
{
if (lean_obj_tag(x_269) == 1)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_inc_ref(x_269);
lean_inc(x_268);
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_269, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 2);
lean_inc_ref(x_274);
lean_inc(x_267);
x_275 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_267, x_254, x_262);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
lean_inc(x_273);
x_277 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_277, 0, x_273);
lean_inc(x_273);
lean_inc(x_267);
x_278 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_278, 0, x_267);
lean_closure_set(x_278, 1, x_273);
x_279 = 0;
x_280 = lean_unbox(x_276);
lean_dec(x_276);
x_281 = l_Lean_instBEqLBool_beq(x_280, x_279);
if (x_281 == 0)
{
x_224 = x_272;
x_225 = x_278;
x_226 = x_269;
x_227 = x_277;
x_228 = x_268;
x_229 = x_267;
x_230 = x_274;
x_231 = x_273;
x_232 = x_254;
x_233 = x_255;
x_234 = x_256;
x_235 = x_257;
x_236 = x_258;
x_237 = x_259;
x_238 = x_260;
x_239 = x_261;
x_240 = x_262;
x_241 = x_263;
x_242 = lean_box(0);
goto block_253;
}
else
{
lean_object* x_282; 
lean_inc(x_273);
x_282 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_273, x_254);
if (lean_obj_tag(x_282) == 0)
{
lean_dec_ref(x_282);
x_224 = x_272;
x_225 = x_278;
x_226 = x_269;
x_227 = x_277;
x_228 = x_268;
x_229 = x_267;
x_230 = x_274;
x_231 = x_273;
x_232 = x_254;
x_233 = x_255;
x_234 = x_256;
x_235 = x_257;
x_236 = x_258;
x_237 = x_259;
x_238 = x_260;
x_239 = x_261;
x_240 = x_262;
x_241 = x_263;
x_242 = lean_box(0);
goto block_253;
}
else
{
lean_dec_ref(x_278);
lean_dec_ref(x_277);
lean_dec_ref(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec_ref(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_283 = !lean_is_exclusive(x_275);
if (x_283 == 0)
{
return x_275;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_275, 0);
lean_inc(x_284);
lean_dec(x_275);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
else
{
lean_object* x_286; 
x_286 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_267, x_254, x_255, x_256, x_257, x_258, x_259, x_260, x_261, x_262, x_263);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
x_287 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5));
x_288 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_287, x_262);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = lean_unbox(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_254);
x_45 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_291; 
x_291 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_267, x_254, x_262);
lean_dec(x_254);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_287, x_292, x_260, x_261, x_262, x_263);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
if (lean_obj_tag(x_293) == 0)
{
lean_dec_ref(x_293);
x_45 = lean_box(0);
goto block_48;
}
else
{
return x_293;
}
}
else
{
uint8_t x_294; 
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
x_294 = !lean_is_exclusive(x_291);
if (x_294 == 0)
{
return x_291;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_254);
x_297 = !lean_is_exclusive(x_288);
if (x_297 == 0)
{
return x_288;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_288, 0);
lean_inc(x_298);
lean_dec(x_288);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7));
x_301 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_300, x_262);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
lean_dec_ref(x_301);
x_303 = lean_unbox(x_302);
lean_dec(x_302);
if (x_303 == 0)
{
x_13 = x_267;
x_14 = x_254;
x_15 = x_255;
x_16 = x_256;
x_17 = x_257;
x_18 = x_258;
x_19 = x_259;
x_20 = x_260;
x_21 = x_261;
x_22 = x_262;
x_23 = x_263;
x_24 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_304; 
lean_inc(x_267);
x_304 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_267, x_254, x_262);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_300, x_305, x_260, x_261, x_262, x_263);
if (lean_obj_tag(x_306) == 0)
{
lean_dec_ref(x_306);
x_13 = x_267;
x_14 = x_254;
x_15 = x_255;
x_16 = x_256;
x_17 = x_257;
x_18 = x_258;
x_19 = x_259;
x_20 = x_260;
x_21 = x_261;
x_22 = x_262;
x_23 = x_263;
x_24 = lean_box(0);
goto block_32;
}
else
{
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
return x_306;
}
}
else
{
uint8_t x_307; 
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_307 = !lean_is_exclusive(x_304);
if (x_307 == 0)
{
return x_304;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_304, 0);
lean_inc(x_308);
lean_dec(x_304);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_267);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_310 = !lean_is_exclusive(x_301);
if (x_310 == 0)
{
return x_301;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_301, 0);
lean_inc(x_311);
lean_dec(x_301);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
}
}
else
{
uint8_t x_313; 
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_313 = !lean_is_exclusive(x_266);
if (x_313 == 0)
{
return x_266;
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_266, 0);
lean_inc(x_314);
lean_dec(x_266);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_314);
return x_315;
}
}
}
}
else
{
uint8_t x_324; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_324 = !lean_is_exclusive(x_221);
if (x_324 == 0)
{
return x_221;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_221, 0);
lean_inc(x_325);
lean_dec(x_221);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
return x_326;
}
}
block_219:
{
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_82);
lean_dec_ref(x_74);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_ctor_get(x_91, 1);
lean_inc_ref(x_92);
if (lean_obj_tag(x_92) == 1)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_94 = lean_ctor_get(x_91, 0);
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 2);
x_97 = lean_ctor_get(x_92, 1);
lean_dec(x_97);
x_98 = lean_int_mul(x_72, x_94);
x_99 = lean_int_mul(x_95, x_85);
x_100 = l_Lean_Meta_Grind_Arith_gcdExt(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_100, 1);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_102, 0);
x_106 = lean_ctor_get(x_102, 1);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_108 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_107, x_75, x_77);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_108);
x_109 = lean_int_mul(x_105, x_94);
lean_dec(x_105);
lean_inc_ref(x_80);
x_110 = l_Int_Linear_Poly_mul(x_80, x_109);
lean_dec(x_109);
x_111 = lean_int_mul(x_106, x_85);
lean_dec(x_106);
lean_inc_ref(x_96);
x_112 = l_Int_Linear_Poly_mul(x_96, x_111);
lean_dec(x_111);
x_113 = lean_int_mul(x_85, x_94);
lean_dec(x_85);
x_114 = l_Int_Linear_Poly_combine(x_110, x_112);
lean_inc(x_104);
lean_ctor_set(x_92, 2, x_114);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 0, x_104);
lean_inc(x_91);
lean_inc_ref(x_86);
lean_ctor_set_tag(x_102, 4);
lean_ctor_set(x_102, 1, x_91);
lean_ctor_set(x_102, 0, x_86);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_92);
lean_ctor_set(x_115, 2, x_102);
lean_inc(x_76);
lean_inc_ref(x_71);
lean_inc(x_89);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_79);
lean_inc(x_87);
lean_inc_ref(x_84);
lean_inc(x_81);
lean_inc(x_77);
x_116 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_115, x_77, x_81, x_84, x_87, x_79, x_83, x_78, x_89, x_71, x_76);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec_ref(x_116);
x_117 = l_Int_Linear_Poly_mul(x_80, x_95);
lean_dec(x_95);
x_118 = lean_int_neg(x_72);
lean_dec(x_72);
x_119 = l_Int_Linear_Poly_mul(x_96, x_118);
lean_dec(x_118);
x_120 = l_Int_Linear_Poly_combine(x_117, x_119);
lean_inc(x_91);
lean_ctor_set_tag(x_100, 5);
lean_ctor_set(x_100, 1, x_91);
lean_ctor_set(x_100, 0, x_86);
x_121 = !lean_is_exclusive(x_91);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_91, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_91, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_91, 0);
lean_dec(x_124);
lean_ctor_set(x_91, 2, x_100);
lean_ctor_set(x_91, 1, x_120);
lean_ctor_set(x_91, 0, x_104);
x_1 = x_91;
x_2 = x_77;
x_3 = x_81;
x_4 = x_84;
x_5 = x_87;
x_6 = x_79;
x_7 = x_83;
x_8 = x_78;
x_9 = x_89;
x_10 = x_71;
x_11 = x_76;
goto _start;
}
else
{
lean_object* x_126; 
lean_dec(x_91);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_104);
lean_ctor_set(x_126, 1, x_120);
lean_ctor_set(x_126, 2, x_100);
x_1 = x_126;
x_2 = x_77;
x_3 = x_81;
x_4 = x_84;
x_5 = x_87;
x_6 = x_79;
x_7 = x_83;
x_8 = x_78;
x_9 = x_89;
x_10 = x_71;
x_11 = x_76;
goto _start;
}
}
else
{
lean_free_object(x_100);
lean_dec(x_104);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_116;
}
}
else
{
lean_free_object(x_102);
lean_dec(x_106);
lean_dec(x_105);
lean_free_object(x_100);
lean_dec(x_104);
lean_free_object(x_92);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_108;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_100, 0);
x_129 = lean_ctor_get(x_102, 0);
x_130 = lean_ctor_get(x_102, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_102);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_132 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_131, x_75, x_77);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_132);
x_133 = lean_int_mul(x_129, x_94);
lean_dec(x_129);
lean_inc_ref(x_80);
x_134 = l_Int_Linear_Poly_mul(x_80, x_133);
lean_dec(x_133);
x_135 = lean_int_mul(x_130, x_85);
lean_dec(x_130);
lean_inc_ref(x_96);
x_136 = l_Int_Linear_Poly_mul(x_96, x_135);
lean_dec(x_135);
x_137 = lean_int_mul(x_85, x_94);
lean_dec(x_85);
x_138 = l_Int_Linear_Poly_combine(x_134, x_136);
lean_inc(x_128);
lean_ctor_set(x_92, 2, x_138);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 0, x_128);
lean_inc(x_91);
lean_inc_ref(x_86);
x_139 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_139, 0, x_86);
lean_ctor_set(x_139, 1, x_91);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_92);
lean_ctor_set(x_140, 2, x_139);
lean_inc(x_76);
lean_inc_ref(x_71);
lean_inc(x_89);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_79);
lean_inc(x_87);
lean_inc_ref(x_84);
lean_inc(x_81);
lean_inc(x_77);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_140, x_77, x_81, x_84, x_87, x_79, x_83, x_78, x_89, x_71, x_76);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_141);
x_142 = l_Int_Linear_Poly_mul(x_80, x_95);
lean_dec(x_95);
x_143 = lean_int_neg(x_72);
lean_dec(x_72);
x_144 = l_Int_Linear_Poly_mul(x_96, x_143);
lean_dec(x_143);
x_145 = l_Int_Linear_Poly_combine(x_142, x_144);
lean_inc(x_91);
lean_ctor_set_tag(x_100, 5);
lean_ctor_set(x_100, 1, x_91);
lean_ctor_set(x_100, 0, x_86);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 x_146 = x_91;
} else {
 lean_dec_ref(x_91);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 3, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_100);
x_1 = x_147;
x_2 = x_77;
x_3 = x_81;
x_4 = x_84;
x_5 = x_87;
x_6 = x_79;
x_7 = x_83;
x_8 = x_78;
x_9 = x_89;
x_10 = x_71;
x_11 = x_76;
goto _start;
}
else
{
lean_free_object(x_100);
lean_dec(x_128);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_141;
}
}
else
{
lean_dec(x_130);
lean_dec(x_129);
lean_free_object(x_100);
lean_dec(x_128);
lean_free_object(x_92);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_132;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_100, 1);
x_150 = lean_ctor_get(x_100, 0);
lean_inc(x_149);
lean_inc(x_150);
lean_dec(x_100);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_155 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_154, x_75, x_77);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_155);
x_156 = lean_int_mul(x_151, x_94);
lean_dec(x_151);
lean_inc_ref(x_80);
x_157 = l_Int_Linear_Poly_mul(x_80, x_156);
lean_dec(x_156);
x_158 = lean_int_mul(x_152, x_85);
lean_dec(x_152);
lean_inc_ref(x_96);
x_159 = l_Int_Linear_Poly_mul(x_96, x_158);
lean_dec(x_158);
x_160 = lean_int_mul(x_85, x_94);
lean_dec(x_85);
x_161 = l_Int_Linear_Poly_combine(x_157, x_159);
lean_inc(x_150);
lean_ctor_set(x_92, 2, x_161);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 0, x_150);
lean_inc(x_91);
lean_inc_ref(x_86);
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(4, 2, 0);
} else {
 x_162 = x_153;
 lean_ctor_set_tag(x_162, 4);
}
lean_ctor_set(x_162, 0, x_86);
lean_ctor_set(x_162, 1, x_91);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_92);
lean_ctor_set(x_163, 2, x_162);
lean_inc(x_76);
lean_inc_ref(x_71);
lean_inc(x_89);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_79);
lean_inc(x_87);
lean_inc_ref(x_84);
lean_inc(x_81);
lean_inc(x_77);
x_164 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_163, x_77, x_81, x_84, x_87, x_79, x_83, x_78, x_89, x_71, x_76);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_164);
x_165 = l_Int_Linear_Poly_mul(x_80, x_95);
lean_dec(x_95);
x_166 = lean_int_neg(x_72);
lean_dec(x_72);
x_167 = l_Int_Linear_Poly_mul(x_96, x_166);
lean_dec(x_166);
x_168 = l_Int_Linear_Poly_combine(x_165, x_167);
lean_inc(x_91);
x_169 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_169, 0, x_86);
lean_ctor_set(x_169, 1, x_91);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 x_170 = x_91;
} else {
 lean_dec_ref(x_91);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_150);
lean_ctor_set(x_171, 1, x_168);
lean_ctor_set(x_171, 2, x_169);
x_1 = x_171;
x_2 = x_77;
x_3 = x_81;
x_4 = x_84;
x_5 = x_87;
x_6 = x_79;
x_7 = x_83;
x_8 = x_78;
x_9 = x_89;
x_10 = x_71;
x_11 = x_76;
goto _start;
}
else
{
lean_dec(x_150);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_164;
}
}
else
{
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_free_object(x_92);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_155;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_173 = lean_ctor_get(x_91, 0);
x_174 = lean_ctor_get(x_92, 0);
x_175 = lean_ctor_get(x_92, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_92);
x_176 = lean_int_mul(x_72, x_173);
x_177 = lean_int_mul(x_174, x_85);
x_178 = l_Lean_Meta_Grind_Arith_gcdExt(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_179, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_184 = x_179;
} else {
 lean_dec_ref(x_179);
 x_184 = lean_box(0);
}
x_185 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_186 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_185, x_75, x_77);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec_ref(x_186);
x_187 = lean_int_mul(x_182, x_173);
lean_dec(x_182);
lean_inc_ref(x_80);
x_188 = l_Int_Linear_Poly_mul(x_80, x_187);
lean_dec(x_187);
x_189 = lean_int_mul(x_183, x_85);
lean_dec(x_183);
lean_inc_ref(x_175);
x_190 = l_Int_Linear_Poly_mul(x_175, x_189);
lean_dec(x_189);
x_191 = lean_int_mul(x_85, x_173);
lean_dec(x_85);
x_192 = l_Int_Linear_Poly_combine(x_188, x_190);
lean_inc(x_180);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_180);
lean_ctor_set(x_193, 1, x_88);
lean_ctor_set(x_193, 2, x_192);
lean_inc(x_91);
lean_inc_ref(x_86);
if (lean_is_scalar(x_184)) {
 x_194 = lean_alloc_ctor(4, 2, 0);
} else {
 x_194 = x_184;
 lean_ctor_set_tag(x_194, 4);
}
lean_ctor_set(x_194, 0, x_86);
lean_ctor_set(x_194, 1, x_91);
x_195 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_195, 2, x_194);
lean_inc(x_76);
lean_inc_ref(x_71);
lean_inc(x_89);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_79);
lean_inc(x_87);
lean_inc_ref(x_84);
lean_inc(x_81);
lean_inc(x_77);
x_196 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_195, x_77, x_81, x_84, x_87, x_79, x_83, x_78, x_89, x_71, x_76);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec_ref(x_196);
x_197 = l_Int_Linear_Poly_mul(x_80, x_174);
lean_dec(x_174);
x_198 = lean_int_neg(x_72);
lean_dec(x_72);
x_199 = l_Int_Linear_Poly_mul(x_175, x_198);
lean_dec(x_198);
x_200 = l_Int_Linear_Poly_combine(x_197, x_199);
lean_inc(x_91);
if (lean_is_scalar(x_181)) {
 x_201 = lean_alloc_ctor(5, 2, 0);
} else {
 x_201 = x_181;
 lean_ctor_set_tag(x_201, 5);
}
lean_ctor_set(x_201, 0, x_86);
lean_ctor_set(x_201, 1, x_91);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 x_202 = x_91;
} else {
 lean_dec_ref(x_91);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 3, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_180);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_203, 2, x_201);
x_1 = x_203;
x_2 = x_77;
x_3 = x_81;
x_4 = x_84;
x_5 = x_87;
x_6 = x_79;
x_7 = x_83;
x_8 = x_78;
x_9 = x_89;
x_10 = x_71;
x_11 = x_76;
goto _start;
}
else
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_196;
}
}
else
{
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec_ref(x_71);
return x_186;
}
}
}
else
{
lean_object* x_205; 
lean_dec_ref(x_92);
lean_dec(x_88);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_80);
lean_dec_ref(x_75);
lean_dec(x_72);
x_205 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_91, x_77, x_81, x_84, x_87, x_79, x_83, x_78, x_89, x_71, x_76);
lean_dec(x_76);
lean_dec_ref(x_71);
lean_dec(x_89);
lean_dec_ref(x_78);
lean_dec(x_83);
lean_dec_ref(x_79);
lean_dec(x_87);
lean_dec_ref(x_84);
lean_dec(x_81);
lean_dec(x_77);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_75);
lean_dec(x_72);
x_206 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
x_207 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_206, x_71);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_dec_ref(x_86);
x_33 = x_82;
x_34 = x_74;
x_35 = x_77;
x_36 = x_78;
x_37 = x_89;
x_38 = x_71;
x_39 = x_76;
x_40 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_210; 
x_210 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_86, x_77, x_71);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_206, x_211, x_78, x_89, x_71, x_76);
if (lean_obj_tag(x_212) == 0)
{
lean_dec_ref(x_212);
x_33 = x_82;
x_34 = x_74;
x_35 = x_77;
x_36 = x_78;
x_37 = x_89;
x_38 = x_71;
x_39 = x_76;
x_40 = lean_box(0);
goto block_44;
}
else
{
lean_dec(x_89);
lean_dec_ref(x_82);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
return x_212;
}
}
else
{
uint8_t x_213; 
lean_dec(x_89);
lean_dec_ref(x_82);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
x_213 = !lean_is_exclusive(x_210);
if (x_213 == 0)
{
return x_210;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
lean_dec(x_210);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_89);
lean_dec_ref(x_86);
lean_dec_ref(x_82);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
x_216 = !lean_is_exclusive(x_207);
if (x_216 == 0)
{
return x_207;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_207, 0);
lean_inc(x_217);
lean_dec(x_207);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
}
}
else
{
lean_object* x_327; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_327 = lean_box(0);
lean_ctor_set(x_67, 0, x_327);
return x_67;
}
}
else
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_ctor_get(x_67, 0);
lean_inc(x_328);
lean_dec(x_67);
x_329 = lean_unbox(x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_400; lean_object* x_401; 
x_400 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
x_401 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_400, x_10);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_497; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec_ref(x_401);
x_403 = lean_box(0);
x_497 = lean_unbox(x_402);
lean_dec(x_402);
if (x_497 == 0)
{
x_434 = x_2;
x_435 = x_3;
x_436 = x_4;
x_437 = x_5;
x_438 = x_6;
x_439 = x_7;
x_440 = x_8;
x_441 = x_9;
x_442 = x_10;
x_443 = x_11;
x_444 = lean_box(0);
goto block_496;
}
else
{
lean_object* x_498; 
lean_inc_ref(x_1);
x_498 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_10);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
lean_dec_ref(x_498);
x_500 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_400, x_499, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
x_434 = x_2;
x_435 = x_3;
x_436 = x_4;
x_437 = x_5;
x_438 = x_6;
x_439 = x_7;
x_440 = x_8;
x_441 = x_9;
x_442 = x_10;
x_443 = x_11;
x_444 = lean_box(0);
goto block_496;
}
else
{
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_501 = lean_ctor_get(x_498, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 x_502 = x_498;
} else {
 lean_dec_ref(x_498);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 1, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_501);
return x_503;
}
}
block_433:
{
lean_object* x_423; 
x_423 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_412, x_420);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
lean_dec_ref(x_423);
x_425 = lean_ctor_get(x_424, 6);
lean_inc_ref(x_425);
lean_dec(x_424);
x_426 = lean_ctor_get(x_425, 2);
x_427 = lean_nat_dec_lt(x_411, x_426);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec_ref(x_425);
x_428 = l_outOfBounds___redArg(x_403);
x_330 = x_420;
x_331 = x_404;
x_332 = lean_box(0);
x_333 = x_406;
x_334 = x_407;
x_335 = x_421;
x_336 = x_412;
x_337 = x_418;
x_338 = x_416;
x_339 = x_410;
x_340 = x_413;
x_341 = x_405;
x_342 = x_417;
x_343 = x_414;
x_344 = x_408;
x_345 = x_409;
x_346 = x_415;
x_347 = x_411;
x_348 = x_419;
x_349 = x_428;
goto block_399;
}
else
{
lean_object* x_429; 
x_429 = l_Lean_PersistentArray_get_x21___redArg(x_403, x_425, x_411);
x_330 = x_420;
x_331 = x_404;
x_332 = lean_box(0);
x_333 = x_406;
x_334 = x_407;
x_335 = x_421;
x_336 = x_412;
x_337 = x_418;
x_338 = x_416;
x_339 = x_410;
x_340 = x_413;
x_341 = x_405;
x_342 = x_417;
x_343 = x_414;
x_344 = x_408;
x_345 = x_409;
x_346 = x_415;
x_347 = x_411;
x_348 = x_419;
x_349 = x_429;
goto block_399;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_421);
lean_dec_ref(x_420);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec_ref(x_406);
lean_dec_ref(x_405);
lean_dec(x_404);
x_430 = lean_ctor_get(x_423, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_431 = x_423;
} else {
 lean_dec_ref(x_423);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
block_496:
{
lean_object* x_445; lean_object* x_446; 
x_445 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_442);
x_446 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_445, x_434, x_435, x_436, x_437, x_438, x_439, x_440, x_441, x_442, x_443);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
x_448 = lean_ctor_get(x_447, 0);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
x_450 = l_Int_Linear_Poly_isUnsatDvd(x_448, x_449);
if (x_450 == 0)
{
uint8_t x_451; 
x_451 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_447);
if (x_451 == 0)
{
if (lean_obj_tag(x_449) == 1)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_inc_ref(x_449);
lean_inc(x_448);
x_452 = lean_ctor_get(x_449, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_449, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_449, 2);
lean_inc_ref(x_454);
lean_inc(x_447);
x_455 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_447, x_434, x_442);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
lean_dec_ref(x_455);
lean_inc(x_453);
x_457 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_457, 0, x_453);
lean_inc(x_453);
lean_inc(x_447);
x_458 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_458, 0, x_447);
lean_closure_set(x_458, 1, x_453);
x_459 = 0;
x_460 = lean_unbox(x_456);
lean_dec(x_456);
x_461 = l_Lean_instBEqLBool_beq(x_460, x_459);
if (x_461 == 0)
{
x_404 = x_452;
x_405 = x_458;
x_406 = x_449;
x_407 = x_457;
x_408 = x_448;
x_409 = x_447;
x_410 = x_454;
x_411 = x_453;
x_412 = x_434;
x_413 = x_435;
x_414 = x_436;
x_415 = x_437;
x_416 = x_438;
x_417 = x_439;
x_418 = x_440;
x_419 = x_441;
x_420 = x_442;
x_421 = x_443;
x_422 = lean_box(0);
goto block_433;
}
else
{
lean_object* x_462; 
lean_inc(x_453);
x_462 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_453, x_434);
if (lean_obj_tag(x_462) == 0)
{
lean_dec_ref(x_462);
x_404 = x_452;
x_405 = x_458;
x_406 = x_449;
x_407 = x_457;
x_408 = x_448;
x_409 = x_447;
x_410 = x_454;
x_411 = x_453;
x_412 = x_434;
x_413 = x_435;
x_414 = x_436;
x_415 = x_437;
x_416 = x_438;
x_417 = x_439;
x_418 = x_440;
x_419 = x_441;
x_420 = x_442;
x_421 = x_443;
x_422 = lean_box(0);
goto block_433;
}
else
{
lean_dec_ref(x_458);
lean_dec_ref(x_457);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
return x_462;
}
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
x_463 = lean_ctor_get(x_455, 0);
lean_inc(x_463);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_464 = x_455;
} else {
 lean_dec_ref(x_455);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 1, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_463);
return x_465;
}
}
else
{
lean_object* x_466; 
x_466 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_447, x_434, x_435, x_436, x_437, x_438, x_439, x_440, x_441, x_442, x_443);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; 
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
x_467 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5));
x_468 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_467, x_442);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; uint8_t x_470; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_dec_ref(x_468);
x_470 = lean_unbox(x_469);
lean_dec(x_469);
if (x_470 == 0)
{
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_434);
x_45 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_471; 
x_471 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_447, x_434, x_442);
lean_dec(x_434);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
lean_dec_ref(x_471);
x_473 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_467, x_472, x_440, x_441, x_442, x_443);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
if (lean_obj_tag(x_473) == 0)
{
lean_dec_ref(x_473);
x_45 = lean_box(0);
goto block_48;
}
else
{
return x_473;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 x_475 = x_471;
} else {
 lean_dec_ref(x_471);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 1, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_474);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_434);
x_477 = lean_ctor_get(x_468, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 x_478 = x_468;
} else {
 lean_dec_ref(x_468);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 1, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_477);
return x_479;
}
}
}
else
{
lean_object* x_480; lean_object* x_481; 
x_480 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7));
x_481 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_480, x_442);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; uint8_t x_483; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
lean_dec_ref(x_481);
x_483 = lean_unbox(x_482);
lean_dec(x_482);
if (x_483 == 0)
{
x_13 = x_447;
x_14 = x_434;
x_15 = x_435;
x_16 = x_436;
x_17 = x_437;
x_18 = x_438;
x_19 = x_439;
x_20 = x_440;
x_21 = x_441;
x_22 = x_442;
x_23 = x_443;
x_24 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_484; 
lean_inc(x_447);
x_484 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_447, x_434, x_442);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
lean_dec_ref(x_484);
x_486 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_480, x_485, x_440, x_441, x_442, x_443);
if (lean_obj_tag(x_486) == 0)
{
lean_dec_ref(x_486);
x_13 = x_447;
x_14 = x_434;
x_15 = x_435;
x_16 = x_436;
x_17 = x_437;
x_18 = x_438;
x_19 = x_439;
x_20 = x_440;
x_21 = x_441;
x_22 = x_442;
x_23 = x_443;
x_24 = lean_box(0);
goto block_32;
}
else
{
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
x_487 = lean_ctor_get(x_484, 0);
lean_inc(x_487);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 x_488 = x_484;
} else {
 lean_dec_ref(x_484);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 1, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_487);
return x_489;
}
}
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_447);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
x_490 = lean_ctor_get(x_481, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_491 = x_481;
} else {
 lean_dec_ref(x_481);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 1, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_490);
return x_492;
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec(x_435);
lean_dec(x_434);
x_493 = lean_ctor_get(x_446, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_494 = x_446;
} else {
 lean_dec_ref(x_446);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 1, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_493);
return x_495;
}
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_504 = lean_ctor_get(x_401, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 x_505 = x_401;
} else {
 lean_dec_ref(x_401);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_504);
return x_506;
}
block_399:
{
if (lean_obj_tag(x_349) == 1)
{
lean_object* x_350; lean_object* x_351; 
lean_dec_ref(x_341);
lean_dec_ref(x_333);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
x_351 = lean_ctor_get(x_350, 1);
lean_inc_ref(x_351);
if (lean_obj_tag(x_351) == 1)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_352 = lean_ctor_get(x_350, 0);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 2);
lean_inc_ref(x_354);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 x_355 = x_351;
} else {
 lean_dec_ref(x_351);
 x_355 = lean_box(0);
}
x_356 = lean_int_mul(x_331, x_352);
x_357 = lean_int_mul(x_353, x_344);
x_358 = l_Lean_Meta_Grind_Arith_gcdExt(x_356, x_357);
lean_dec(x_357);
lean_dec(x_356);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_361 = x_358;
} else {
 lean_dec_ref(x_358);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_364 = x_359;
} else {
 lean_dec_ref(x_359);
 x_364 = lean_box(0);
}
x_365 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_366 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_365, x_334, x_336);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec_ref(x_366);
x_367 = lean_int_mul(x_362, x_352);
lean_dec(x_362);
lean_inc_ref(x_339);
x_368 = l_Int_Linear_Poly_mul(x_339, x_367);
lean_dec(x_367);
x_369 = lean_int_mul(x_363, x_344);
lean_dec(x_363);
lean_inc_ref(x_354);
x_370 = l_Int_Linear_Poly_mul(x_354, x_369);
lean_dec(x_369);
x_371 = lean_int_mul(x_344, x_352);
lean_dec(x_344);
x_372 = l_Int_Linear_Poly_combine(x_368, x_370);
lean_inc(x_360);
if (lean_is_scalar(x_355)) {
 x_373 = lean_alloc_ctor(1, 3, 0);
} else {
 x_373 = x_355;
}
lean_ctor_set(x_373, 0, x_360);
lean_ctor_set(x_373, 1, x_347);
lean_ctor_set(x_373, 2, x_372);
lean_inc(x_350);
lean_inc_ref(x_345);
if (lean_is_scalar(x_364)) {
 x_374 = lean_alloc_ctor(4, 2, 0);
} else {
 x_374 = x_364;
 lean_ctor_set_tag(x_374, 4);
}
lean_ctor_set(x_374, 0, x_345);
lean_ctor_set(x_374, 1, x_350);
x_375 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_375, 0, x_371);
lean_ctor_set(x_375, 1, x_373);
lean_ctor_set(x_375, 2, x_374);
lean_inc(x_335);
lean_inc_ref(x_330);
lean_inc(x_348);
lean_inc_ref(x_337);
lean_inc(x_342);
lean_inc_ref(x_338);
lean_inc(x_346);
lean_inc_ref(x_343);
lean_inc(x_340);
lean_inc(x_336);
x_376 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_375, x_336, x_340, x_343, x_346, x_338, x_342, x_337, x_348, x_330, x_335);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec_ref(x_376);
x_377 = l_Int_Linear_Poly_mul(x_339, x_353);
lean_dec(x_353);
x_378 = lean_int_neg(x_331);
lean_dec(x_331);
x_379 = l_Int_Linear_Poly_mul(x_354, x_378);
lean_dec(x_378);
x_380 = l_Int_Linear_Poly_combine(x_377, x_379);
lean_inc(x_350);
if (lean_is_scalar(x_361)) {
 x_381 = lean_alloc_ctor(5, 2, 0);
} else {
 x_381 = x_361;
 lean_ctor_set_tag(x_381, 5);
}
lean_ctor_set(x_381, 0, x_345);
lean_ctor_set(x_381, 1, x_350);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 x_382 = x_350;
} else {
 lean_dec_ref(x_350);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(0, 3, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_360);
lean_ctor_set(x_383, 1, x_380);
lean_ctor_set(x_383, 2, x_381);
x_1 = x_383;
x_2 = x_336;
x_3 = x_340;
x_4 = x_343;
x_5 = x_346;
x_6 = x_338;
x_7 = x_342;
x_8 = x_337;
x_9 = x_348;
x_10 = x_330;
x_11 = x_335;
goto _start;
}
else
{
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_331);
lean_dec_ref(x_330);
return x_376;
}
}
else
{
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_331);
lean_dec_ref(x_330);
return x_366;
}
}
else
{
lean_object* x_385; 
lean_dec_ref(x_351);
lean_dec(x_347);
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_339);
lean_dec_ref(x_334);
lean_dec(x_331);
x_385 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_350, x_336, x_340, x_343, x_346, x_338, x_342, x_337, x_348, x_330, x_335);
lean_dec(x_335);
lean_dec_ref(x_330);
lean_dec(x_348);
lean_dec_ref(x_337);
lean_dec(x_342);
lean_dec_ref(x_338);
lean_dec(x_346);
lean_dec_ref(x_343);
lean_dec(x_340);
lean_dec(x_336);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_334);
lean_dec(x_331);
x_386 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
x_387 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_386, x_330);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; uint8_t x_389; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
lean_dec_ref(x_387);
x_389 = lean_unbox(x_388);
lean_dec(x_388);
if (x_389 == 0)
{
lean_dec_ref(x_345);
x_33 = x_341;
x_34 = x_333;
x_35 = x_336;
x_36 = x_337;
x_37 = x_348;
x_38 = x_330;
x_39 = x_335;
x_40 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_390; 
x_390 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_345, x_336, x_330);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_386, x_391, x_337, x_348, x_330, x_335);
if (lean_obj_tag(x_392) == 0)
{
lean_dec_ref(x_392);
x_33 = x_341;
x_34 = x_333;
x_35 = x_336;
x_36 = x_337;
x_37 = x_348;
x_38 = x_330;
x_39 = x_335;
x_40 = lean_box(0);
goto block_44;
}
else
{
lean_dec(x_348);
lean_dec_ref(x_341);
lean_dec_ref(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_333);
lean_dec_ref(x_330);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_348);
lean_dec_ref(x_341);
lean_dec_ref(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_333);
lean_dec_ref(x_330);
x_393 = lean_ctor_get(x_390, 0);
lean_inc(x_393);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_394 = x_390;
} else {
 lean_dec_ref(x_390);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 1, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_393);
return x_395;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_348);
lean_dec_ref(x_345);
lean_dec_ref(x_341);
lean_dec_ref(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_333);
lean_dec_ref(x_330);
x_396 = lean_ctor_get(x_387, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_397 = x_387;
} else {
 lean_dec_ref(x_387);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 1, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_396);
return x_398;
}
}
}
}
else
{
lean_object* x_507; lean_object* x_508; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_507 = lean_box(0);
x_508 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_508, 0, x_507);
return x_508;
}
}
}
else
{
uint8_t x_509; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_509 = !lean_is_exclusive(x_67);
if (x_509 == 0)
{
return x_67;
}
else
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_67, 0);
lean_inc(x_510);
lean_dec(x_67);
x_511 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_511, 0, x_510);
return x_511;
}
}
}
else
{
lean_object* x_512; 
lean_free_object(x_10);
lean_dec_ref(x_63);
lean_dec(x_62);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_512 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_55);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; uint8_t x_529; 
x_513 = lean_ctor_get(x_10, 0);
x_514 = lean_ctor_get(x_10, 1);
x_515 = lean_ctor_get(x_10, 2);
x_516 = lean_ctor_get(x_10, 3);
x_517 = lean_ctor_get(x_10, 4);
x_518 = lean_ctor_get(x_10, 5);
x_519 = lean_ctor_get(x_10, 6);
x_520 = lean_ctor_get(x_10, 7);
x_521 = lean_ctor_get(x_10, 8);
x_522 = lean_ctor_get(x_10, 9);
x_523 = lean_ctor_get(x_10, 10);
x_524 = lean_ctor_get(x_10, 11);
x_525 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_526 = lean_ctor_get(x_10, 12);
x_527 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_528 = lean_ctor_get(x_10, 13);
lean_inc(x_528);
lean_inc(x_526);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
lean_inc(x_520);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_10);
x_529 = lean_nat_dec_eq(x_516, x_517);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(1u);
x_531 = lean_nat_add(x_516, x_530);
lean_dec(x_516);
x_532 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_532, 0, x_513);
lean_ctor_set(x_532, 1, x_514);
lean_ctor_set(x_532, 2, x_515);
lean_ctor_set(x_532, 3, x_531);
lean_ctor_set(x_532, 4, x_517);
lean_ctor_set(x_532, 5, x_518);
lean_ctor_set(x_532, 6, x_519);
lean_ctor_set(x_532, 7, x_520);
lean_ctor_set(x_532, 8, x_521);
lean_ctor_set(x_532, 9, x_522);
lean_ctor_set(x_532, 10, x_523);
lean_ctor_set(x_532, 11, x_524);
lean_ctor_set(x_532, 12, x_526);
lean_ctor_set(x_532, 13, x_528);
lean_ctor_set_uint8(x_532, sizeof(void*)*14, x_525);
lean_ctor_set_uint8(x_532, sizeof(void*)*14 + 1, x_527);
x_533 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_535 = x_533;
} else {
 lean_dec_ref(x_533);
 x_535 = lean_box(0);
}
x_536 = lean_unbox(x_534);
lean_dec(x_534);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_607; lean_object* x_608; 
lean_dec(x_535);
x_607 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
x_608 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_607, x_532);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_704; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
lean_dec_ref(x_608);
x_610 = lean_box(0);
x_704 = lean_unbox(x_609);
lean_dec(x_609);
if (x_704 == 0)
{
x_641 = x_2;
x_642 = x_3;
x_643 = x_4;
x_644 = x_5;
x_645 = x_6;
x_646 = x_7;
x_647 = x_8;
x_648 = x_9;
x_649 = x_532;
x_650 = x_11;
x_651 = lean_box(0);
goto block_703;
}
else
{
lean_object* x_705; 
lean_inc_ref(x_1);
x_705 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_532);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; 
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
lean_dec_ref(x_705);
x_707 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_607, x_706, x_8, x_9, x_532, x_11);
if (lean_obj_tag(x_707) == 0)
{
lean_dec_ref(x_707);
x_641 = x_2;
x_642 = x_3;
x_643 = x_4;
x_644 = x_5;
x_645 = x_6;
x_646 = x_7;
x_647 = x_8;
x_648 = x_9;
x_649 = x_532;
x_650 = x_11;
x_651 = lean_box(0);
goto block_703;
}
else
{
lean_dec_ref(x_532);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_707;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_dec_ref(x_532);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_708 = lean_ctor_get(x_705, 0);
lean_inc(x_708);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 x_709 = x_705;
} else {
 lean_dec_ref(x_705);
 x_709 = lean_box(0);
}
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(1, 1, 0);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_708);
return x_710;
}
}
block_640:
{
lean_object* x_630; 
x_630 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_619, x_627);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
lean_dec_ref(x_630);
x_632 = lean_ctor_get(x_631, 6);
lean_inc_ref(x_632);
lean_dec(x_631);
x_633 = lean_ctor_get(x_632, 2);
x_634 = lean_nat_dec_lt(x_618, x_633);
if (x_634 == 0)
{
lean_object* x_635; 
lean_dec_ref(x_632);
x_635 = l_outOfBounds___redArg(x_610);
x_537 = x_627;
x_538 = x_611;
x_539 = lean_box(0);
x_540 = x_613;
x_541 = x_614;
x_542 = x_628;
x_543 = x_619;
x_544 = x_625;
x_545 = x_623;
x_546 = x_617;
x_547 = x_620;
x_548 = x_612;
x_549 = x_624;
x_550 = x_621;
x_551 = x_615;
x_552 = x_616;
x_553 = x_622;
x_554 = x_618;
x_555 = x_626;
x_556 = x_635;
goto block_606;
}
else
{
lean_object* x_636; 
x_636 = l_Lean_PersistentArray_get_x21___redArg(x_610, x_632, x_618);
x_537 = x_627;
x_538 = x_611;
x_539 = lean_box(0);
x_540 = x_613;
x_541 = x_614;
x_542 = x_628;
x_543 = x_619;
x_544 = x_625;
x_545 = x_623;
x_546 = x_617;
x_547 = x_620;
x_548 = x_612;
x_549 = x_624;
x_550 = x_621;
x_551 = x_615;
x_552 = x_616;
x_553 = x_622;
x_554 = x_618;
x_555 = x_626;
x_556 = x_636;
goto block_606;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_621);
lean_dec(x_620);
lean_dec(x_619);
lean_dec(x_618);
lean_dec_ref(x_617);
lean_dec_ref(x_616);
lean_dec(x_615);
lean_dec_ref(x_614);
lean_dec_ref(x_613);
lean_dec_ref(x_612);
lean_dec(x_611);
x_637 = lean_ctor_get(x_630, 0);
lean_inc(x_637);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 x_638 = x_630;
} else {
 lean_dec_ref(x_630);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_637);
return x_639;
}
}
block_703:
{
lean_object* x_652; lean_object* x_653; 
x_652 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_649);
x_653 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_652, x_641, x_642, x_643, x_644, x_645, x_646, x_647, x_648, x_649, x_650);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
lean_dec_ref(x_653);
x_655 = lean_ctor_get(x_654, 0);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
x_657 = l_Int_Linear_Poly_isUnsatDvd(x_655, x_656);
if (x_657 == 0)
{
uint8_t x_658; 
x_658 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_654);
if (x_658 == 0)
{
if (lean_obj_tag(x_656) == 1)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_inc_ref(x_656);
lean_inc(x_655);
x_659 = lean_ctor_get(x_656, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_656, 1);
lean_inc(x_660);
x_661 = lean_ctor_get(x_656, 2);
lean_inc_ref(x_661);
lean_inc(x_654);
x_662 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_654, x_641, x_649);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; uint8_t x_667; uint8_t x_668; 
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
lean_dec_ref(x_662);
lean_inc(x_660);
x_664 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_664, 0, x_660);
lean_inc(x_660);
lean_inc(x_654);
x_665 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_665, 0, x_654);
lean_closure_set(x_665, 1, x_660);
x_666 = 0;
x_667 = lean_unbox(x_663);
lean_dec(x_663);
x_668 = l_Lean_instBEqLBool_beq(x_667, x_666);
if (x_668 == 0)
{
x_611 = x_659;
x_612 = x_665;
x_613 = x_656;
x_614 = x_664;
x_615 = x_655;
x_616 = x_654;
x_617 = x_661;
x_618 = x_660;
x_619 = x_641;
x_620 = x_642;
x_621 = x_643;
x_622 = x_644;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_648;
x_627 = x_649;
x_628 = x_650;
x_629 = lean_box(0);
goto block_640;
}
else
{
lean_object* x_669; 
lean_inc(x_660);
x_669 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_660, x_641);
if (lean_obj_tag(x_669) == 0)
{
lean_dec_ref(x_669);
x_611 = x_659;
x_612 = x_665;
x_613 = x_656;
x_614 = x_664;
x_615 = x_655;
x_616 = x_654;
x_617 = x_661;
x_618 = x_660;
x_619 = x_641;
x_620 = x_642;
x_621 = x_643;
x_622 = x_644;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_648;
x_627 = x_649;
x_628 = x_650;
x_629 = lean_box(0);
goto block_640;
}
else
{
lean_dec_ref(x_665);
lean_dec_ref(x_664);
lean_dec_ref(x_661);
lean_dec(x_660);
lean_dec(x_659);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec_ref(x_661);
lean_dec(x_660);
lean_dec(x_659);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
x_670 = lean_ctor_get(x_662, 0);
lean_inc(x_670);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 x_671 = x_662;
} else {
 lean_dec_ref(x_662);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 1, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_670);
return x_672;
}
}
else
{
lean_object* x_673; 
x_673 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_654, x_641, x_642, x_643, x_644, x_645, x_646, x_647, x_648, x_649, x_650);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
x_674 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5));
x_675 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_674, x_649);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; uint8_t x_677; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
lean_dec_ref(x_675);
x_677 = lean_unbox(x_676);
lean_dec(x_676);
if (x_677 == 0)
{
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_641);
x_45 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_678; 
x_678 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_654, x_641, x_649);
lean_dec(x_641);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
lean_dec_ref(x_678);
x_680 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_674, x_679, x_647, x_648, x_649, x_650);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
if (lean_obj_tag(x_680) == 0)
{
lean_dec_ref(x_680);
x_45 = lean_box(0);
goto block_48;
}
else
{
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
x_681 = lean_ctor_get(x_678, 0);
lean_inc(x_681);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 x_682 = x_678;
} else {
 lean_dec_ref(x_678);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(1, 1, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_681);
return x_683;
}
}
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_641);
x_684 = lean_ctor_get(x_675, 0);
lean_inc(x_684);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_685 = x_675;
} else {
 lean_dec_ref(x_675);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 1, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_684);
return x_686;
}
}
}
else
{
lean_object* x_687; lean_object* x_688; 
x_687 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7));
x_688 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_687, x_649);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; uint8_t x_690; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
lean_dec_ref(x_688);
x_690 = lean_unbox(x_689);
lean_dec(x_689);
if (x_690 == 0)
{
x_13 = x_654;
x_14 = x_641;
x_15 = x_642;
x_16 = x_643;
x_17 = x_644;
x_18 = x_645;
x_19 = x_646;
x_20 = x_647;
x_21 = x_648;
x_22 = x_649;
x_23 = x_650;
x_24 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_691; 
lean_inc(x_654);
x_691 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_654, x_641, x_649);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
lean_dec_ref(x_691);
x_693 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_687, x_692, x_647, x_648, x_649, x_650);
if (lean_obj_tag(x_693) == 0)
{
lean_dec_ref(x_693);
x_13 = x_654;
x_14 = x_641;
x_15 = x_642;
x_16 = x_643;
x_17 = x_644;
x_18 = x_645;
x_19 = x_646;
x_20 = x_647;
x_21 = x_648;
x_22 = x_649;
x_23 = x_650;
x_24 = lean_box(0);
goto block_32;
}
else
{
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
x_694 = lean_ctor_get(x_691, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 x_695 = x_691;
} else {
 lean_dec_ref(x_691);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 1, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_654);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
x_697 = lean_ctor_get(x_688, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 x_698 = x_688;
} else {
 lean_dec_ref(x_688);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 1, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_697);
return x_699;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec_ref(x_643);
lean_dec(x_642);
lean_dec(x_641);
x_700 = lean_ctor_get(x_653, 0);
lean_inc(x_700);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 x_701 = x_653;
} else {
 lean_dec_ref(x_653);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 1, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_700);
return x_702;
}
}
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec_ref(x_532);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_711 = lean_ctor_get(x_608, 0);
lean_inc(x_711);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 x_712 = x_608;
} else {
 lean_dec_ref(x_608);
 x_712 = lean_box(0);
}
if (lean_is_scalar(x_712)) {
 x_713 = lean_alloc_ctor(1, 1, 0);
} else {
 x_713 = x_712;
}
lean_ctor_set(x_713, 0, x_711);
return x_713;
}
block_606:
{
if (lean_obj_tag(x_556) == 1)
{
lean_object* x_557; lean_object* x_558; 
lean_dec_ref(x_548);
lean_dec_ref(x_540);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
lean_dec_ref(x_556);
x_558 = lean_ctor_get(x_557, 1);
lean_inc_ref(x_558);
if (lean_obj_tag(x_558) == 1)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_559 = lean_ctor_get(x_557, 0);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_558, 2);
lean_inc_ref(x_561);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 lean_ctor_release(x_558, 2);
 x_562 = x_558;
} else {
 lean_dec_ref(x_558);
 x_562 = lean_box(0);
}
x_563 = lean_int_mul(x_538, x_559);
x_564 = lean_int_mul(x_560, x_551);
x_565 = l_Lean_Meta_Grind_Arith_gcdExt(x_563, x_564);
lean_dec(x_564);
lean_dec(x_563);
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_568 = x_565;
} else {
 lean_dec_ref(x_565);
 x_568 = lean_box(0);
}
x_569 = lean_ctor_get(x_566, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_566, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_571 = x_566;
} else {
 lean_dec_ref(x_566);
 x_571 = lean_box(0);
}
x_572 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_573 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_572, x_541, x_543);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec_ref(x_573);
x_574 = lean_int_mul(x_569, x_559);
lean_dec(x_569);
lean_inc_ref(x_546);
x_575 = l_Int_Linear_Poly_mul(x_546, x_574);
lean_dec(x_574);
x_576 = lean_int_mul(x_570, x_551);
lean_dec(x_570);
lean_inc_ref(x_561);
x_577 = l_Int_Linear_Poly_mul(x_561, x_576);
lean_dec(x_576);
x_578 = lean_int_mul(x_551, x_559);
lean_dec(x_551);
x_579 = l_Int_Linear_Poly_combine(x_575, x_577);
lean_inc(x_567);
if (lean_is_scalar(x_562)) {
 x_580 = lean_alloc_ctor(1, 3, 0);
} else {
 x_580 = x_562;
}
lean_ctor_set(x_580, 0, x_567);
lean_ctor_set(x_580, 1, x_554);
lean_ctor_set(x_580, 2, x_579);
lean_inc(x_557);
lean_inc_ref(x_552);
if (lean_is_scalar(x_571)) {
 x_581 = lean_alloc_ctor(4, 2, 0);
} else {
 x_581 = x_571;
 lean_ctor_set_tag(x_581, 4);
}
lean_ctor_set(x_581, 0, x_552);
lean_ctor_set(x_581, 1, x_557);
x_582 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_582, 0, x_578);
lean_ctor_set(x_582, 1, x_580);
lean_ctor_set(x_582, 2, x_581);
lean_inc(x_542);
lean_inc_ref(x_537);
lean_inc(x_555);
lean_inc_ref(x_544);
lean_inc(x_549);
lean_inc_ref(x_545);
lean_inc(x_553);
lean_inc_ref(x_550);
lean_inc(x_547);
lean_inc(x_543);
x_583 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_582, x_543, x_547, x_550, x_553, x_545, x_549, x_544, x_555, x_537, x_542);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec_ref(x_583);
x_584 = l_Int_Linear_Poly_mul(x_546, x_560);
lean_dec(x_560);
x_585 = lean_int_neg(x_538);
lean_dec(x_538);
x_586 = l_Int_Linear_Poly_mul(x_561, x_585);
lean_dec(x_585);
x_587 = l_Int_Linear_Poly_combine(x_584, x_586);
lean_inc(x_557);
if (lean_is_scalar(x_568)) {
 x_588 = lean_alloc_ctor(5, 2, 0);
} else {
 x_588 = x_568;
 lean_ctor_set_tag(x_588, 5);
}
lean_ctor_set(x_588, 0, x_552);
lean_ctor_set(x_588, 1, x_557);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 lean_ctor_release(x_557, 2);
 x_589 = x_557;
} else {
 lean_dec_ref(x_557);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(0, 3, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_567);
lean_ctor_set(x_590, 1, x_587);
lean_ctor_set(x_590, 2, x_588);
x_1 = x_590;
x_2 = x_543;
x_3 = x_547;
x_4 = x_550;
x_5 = x_553;
x_6 = x_545;
x_7 = x_549;
x_8 = x_544;
x_9 = x_555;
x_10 = x_537;
x_11 = x_542;
goto _start;
}
else
{
lean_dec(x_568);
lean_dec(x_567);
lean_dec_ref(x_561);
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec_ref(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_546);
lean_dec_ref(x_545);
lean_dec_ref(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_538);
lean_dec_ref(x_537);
return x_583;
}
}
else
{
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_562);
lean_dec_ref(x_561);
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec_ref(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_546);
lean_dec_ref(x_545);
lean_dec_ref(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_538);
lean_dec_ref(x_537);
return x_573;
}
}
else
{
lean_object* x_592; 
lean_dec_ref(x_558);
lean_dec(x_554);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec_ref(x_546);
lean_dec_ref(x_541);
lean_dec(x_538);
x_592 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_557, x_543, x_547, x_550, x_553, x_545, x_549, x_544, x_555, x_537, x_542);
lean_dec(x_542);
lean_dec_ref(x_537);
lean_dec(x_555);
lean_dec_ref(x_544);
lean_dec(x_549);
lean_dec_ref(x_545);
lean_dec(x_553);
lean_dec_ref(x_550);
lean_dec(x_547);
lean_dec(x_543);
return x_592;
}
}
else
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_556);
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_551);
lean_dec_ref(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_546);
lean_dec_ref(x_545);
lean_dec_ref(x_541);
lean_dec(x_538);
x_593 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
x_594 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_593, x_537);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; uint8_t x_596; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
lean_dec_ref(x_594);
x_596 = lean_unbox(x_595);
lean_dec(x_595);
if (x_596 == 0)
{
lean_dec_ref(x_552);
x_33 = x_548;
x_34 = x_540;
x_35 = x_543;
x_36 = x_544;
x_37 = x_555;
x_38 = x_537;
x_39 = x_542;
x_40 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_597; 
x_597 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_552, x_543, x_537);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
lean_dec_ref(x_597);
x_599 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_593, x_598, x_544, x_555, x_537, x_542);
if (lean_obj_tag(x_599) == 0)
{
lean_dec_ref(x_599);
x_33 = x_548;
x_34 = x_540;
x_35 = x_543;
x_36 = x_544;
x_37 = x_555;
x_38 = x_537;
x_39 = x_542;
x_40 = lean_box(0);
goto block_44;
}
else
{
lean_dec(x_555);
lean_dec_ref(x_548);
lean_dec_ref(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec_ref(x_540);
lean_dec_ref(x_537);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_555);
lean_dec_ref(x_548);
lean_dec_ref(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec_ref(x_540);
lean_dec_ref(x_537);
x_600 = lean_ctor_get(x_597, 0);
lean_inc(x_600);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 x_601 = x_597;
} else {
 lean_dec_ref(x_597);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 1, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_600);
return x_602;
}
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_555);
lean_dec_ref(x_552);
lean_dec_ref(x_548);
lean_dec_ref(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec_ref(x_540);
lean_dec_ref(x_537);
x_603 = lean_ctor_get(x_594, 0);
lean_inc(x_603);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 x_604 = x_594;
} else {
 lean_dec_ref(x_594);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(1, 1, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_603);
return x_605;
}
}
}
}
else
{
lean_object* x_714; lean_object* x_715; 
lean_dec_ref(x_532);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_714 = lean_box(0);
if (lean_is_scalar(x_535)) {
 x_715 = lean_alloc_ctor(0, 1, 0);
} else {
 x_715 = x_535;
}
lean_ctor_set(x_715, 0, x_714);
return x_715;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec_ref(x_532);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_716 = lean_ctor_get(x_533, 0);
lean_inc(x_716);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_717 = x_533;
} else {
 lean_dec_ref(x_533);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(1, 1, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_716);
return x_718;
}
}
else
{
lean_object* x_719; 
lean_dec_ref(x_528);
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec_ref(x_514);
lean_dec_ref(x_513);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_719 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_518);
return x_719;
}
}
block_32:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_13);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
return x_26;
}
}
block_44:
{
lean_object* x_41; 
x_41 = l_Int_Linear_Poly_updateOccs___redArg(x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_41);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_43 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_42, x_33, x_35);
lean_dec(x_35);
return x_43;
}
else
{
lean_dec(x_35);
lean_dec_ref(x_33);
return x_41;
}
}
block_48:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_14);
x_15 = l_Int_Linear_Poly_normCommRing_x3f(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_16);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
}
else
{
uint8_t x_26; 
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
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_23 = l_Lean_Expr_cleanupAnnotations(x_18);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
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
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
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
goto block_22;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
goto block_22;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
x_36 = l_Lean_Expr_isConstOf(x_34, x_35);
lean_dec_ref(x_34);
if (x_36 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
goto block_22;
}
else
{
lean_object* x_37; 
lean_dec(x_19);
x_37 = l_Lean_Meta_Structural_isInstDvdInt___redArg(x_31, x_9);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; 
lean_free_object(x_37);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_28);
x_42 = l_Lean_Meta_getIntValue_x3f(x_28, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 1)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_1);
x_46 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_free_object(x_43);
lean_dec(x_45);
lean_inc_ref(x_1);
x_49 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_53 = lean_box(0);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; 
lean_free_object(x_49);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_54 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_57 = l_Lean_eagerReflBoolTrue;
x_58 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_55);
x_59 = l_Lean_mkApp4(x_56, x_28, x_25, x_57, x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Meta_Grind_pushNewFact(x_59, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
lean_dec(x_54);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
lean_dec(x_49);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_69 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_72 = l_Lean_eagerReflBoolTrue;
x_73 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_70);
x_74 = l_Lean_mkApp4(x_71, x_28, x_25, x_72, x_73);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Meta_Grind_pushNewFact(x_74, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_80 = !lean_is_exclusive(x_49);
if (x_80 == 0)
{
return x_49;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_49, 0);
lean_inc(x_81);
lean_dec(x_49);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec_ref(x_28);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_ctor_set_tag(x_43, 0);
lean_ctor_set(x_43, 0, x_1);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_45);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_43);
x_86 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_86;
}
else
{
uint8_t x_87; 
lean_free_object(x_43);
lean_dec(x_45);
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
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_free_object(x_43);
lean_dec(x_45);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_90 = !lean_is_exclusive(x_46);
if (x_90 == 0)
{
return x_46;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_46, 0);
lean_inc(x_91);
lean_dec(x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_43, 0);
lean_inc(x_93);
lean_dec(x_43);
lean_inc_ref(x_1);
x_94 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_93);
lean_inc_ref(x_1);
x_97 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_unbox(x_98);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_101 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_99);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_103 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_106 = l_Lean_eagerReflBoolTrue;
x_107 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_104);
x_108 = l_Lean_mkApp4(x_105, x_28, x_25, x_106, x_107);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lean_Meta_Grind_pushNewFact(x_108, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_114 = lean_ctor_get(x_97, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_115 = x_97;
} else {
 lean_dec_ref(x_97);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec_ref(x_28);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_1);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_93);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_119);
x_121 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_93);
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
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_93);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_125 = lean_ctor_get(x_94, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_126 = x_94;
} else {
 lean_dec_ref(x_94);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_43);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec(x_2);
x_128 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = lean_ctor_get_uint8(x_129, sizeof(void*)*11 + 14);
lean_dec(x_129);
if (x_130 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_132 = l_Lean_indentExpr(x_1);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Meta_Grind_reportIssue(x_133, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_134) == 0)
{
lean_dec_ref(x_134);
x_13 = lean_box(0);
goto block_16;
}
else
{
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_135 = !lean_is_exclusive(x_128);
if (x_135 == 0)
{
return x_128;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
lean_dec(x_128);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
}
else
{
uint8_t x_138; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_138 = !lean_is_exclusive(x_42);
if (x_138 == 0)
{
return x_42;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_42, 0);
lean_inc(x_139);
lean_dec(x_42);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
}
else
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_37, 0);
lean_inc(x_141);
lean_dec(x_37);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
else
{
lean_object* x_145; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_28);
x_145 = l_Lean_Meta_getIntValue_x3f(x_28, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
if (lean_obj_tag(x_146) == 1)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
lean_inc_ref(x_1);
x_149 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_148);
lean_dec(x_147);
lean_inc_ref(x_1);
x_152 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_unbox(x_153);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_156 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_154;
}
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_154);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_158 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_161 = l_Lean_eagerReflBoolTrue;
x_162 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_159);
x_163 = l_Lean_mkApp4(x_160, x_28, x_25, x_161, x_162);
x_164 = lean_unsigned_to_nat(0u);
x_165 = l_Lean_Meta_Grind_pushNewFact(x_163, x_164, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_166 = lean_ctor_get(x_158, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_167 = x_158;
} else {
 lean_dec_ref(x_158);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_169 = lean_ctor_get(x_152, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_170 = x_152;
} else {
 lean_dec_ref(x_152);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
else
{
lean_object* x_172; 
lean_dec_ref(x_28);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_172 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
if (lean_is_scalar(x_148)) {
 x_174 = lean_alloc_ctor(0, 1, 0);
} else {
 x_174 = x_148;
 lean_ctor_set_tag(x_174, 0);
}
lean_ctor_set(x_174, 0, x_1);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_147);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_174);
x_176 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_148);
lean_dec(x_147);
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
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_180 = lean_ctor_get(x_149, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_181 = x_149;
} else {
 lean_dec_ref(x_149);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
else
{
lean_object* x_183; 
lean_dec(x_146);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec(x_2);
x_183 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_ctor_get_uint8(x_184, sizeof(void*)*11 + 14);
lean_dec(x_184);
if (x_185 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_187 = l_Lean_indentExpr(x_1);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_Meta_Grind_reportIssue(x_188, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_189) == 0)
{
lean_dec_ref(x_189);
x_13 = lean_box(0);
goto block_16;
}
else
{
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_190 = lean_ctor_get(x_183, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_193 = lean_ctor_get(x_145, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_194 = x_145;
} else {
 lean_dec_ref(x_145);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
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
x_196 = !lean_is_exclusive(x_37);
if (x_196 == 0)
{
return x_37;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_37, 0);
lean_inc(x_197);
lean_dec(x_37);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
}
}
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_199; 
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
x_199 = !lean_is_exclusive(x_17);
if (x_199 == 0)
{
return x_17;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_17, 0);
lean_inc(x_200);
lean_dec(x_17);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_1);
x_21 = l_Lean_Expr_cleanupAnnotations(x_1);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
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
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
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
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Structural_isInstDvdNat___redArg(x_29, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; 
lean_free_object(x_35);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_40 = l_Lean_Meta_getNatValue_x3f(x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc_ref(x_1);
x_43 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_42);
lean_inc_ref(x_1);
x_46 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_50 = lean_box(0);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; 
lean_free_object(x_46);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_51 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_54 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_52);
x_55 = l_Lean_mkApp3(x_53, x_26, x_23, x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Lean_Meta_Grind_pushNewFact(x_55, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_65 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_68 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_66);
x_69 = l_Lean_mkApp3(x_67, x_26, x_23, x_68);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Meta_Grind_pushNewFact(x_69, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_75 = !lean_is_exclusive(x_46);
if (x_75 == 0)
{
return x_46;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_46, 0);
lean_inc(x_76);
lean_dec(x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_26);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_23);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_84);
x_88 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_84, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Int_Linear_Expr_norm(x_89);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_92 = l_Lean_mkApp6(x_91, x_26, x_23, x_80, x_84, x_81, x_85);
lean_inc(x_42);
x_93 = lean_nat_to_int(x_42);
x_94 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_42);
lean_ctor_set(x_94, 3, x_89);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_90);
lean_ctor_set(x_95, 2, x_94);
x_96 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_97 = !lean_is_exclusive(x_88);
if (x_97 == 0)
{
return x_88;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_88, 0);
lean_inc(x_98);
lean_dec(x_88);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_100 = !lean_is_exclusive(x_86);
if (x_100 == 0)
{
return x_86;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_86, 0);
lean_inc(x_101);
lean_dec(x_86);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_103 = !lean_is_exclusive(x_82);
if (x_103 == 0)
{
return x_82;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_82, 0);
lean_inc(x_104);
lean_dec(x_82);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_106 = !lean_is_exclusive(x_78);
if (x_106 == 0)
{
return x_78;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_78, 0);
lean_inc(x_107);
lean_dec(x_78);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_109 = !lean_is_exclusive(x_43);
if (x_109 == 0)
{
return x_43;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_43, 0);
lean_inc(x_110);
lean_dec(x_43);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_41);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_2);
x_112 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_ctor_get_uint8(x_113, sizeof(void*)*11 + 14);
lean_dec(x_113);
if (x_114 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_116 = l_Lean_indentExpr(x_1);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Meta_Grind_reportIssue(x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_118) == 0)
{
lean_dec_ref(x_118);
x_17 = lean_box(0);
goto block_20;
}
else
{
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_119 = !lean_is_exclusive(x_112);
if (x_119 == 0)
{
return x_112;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_112, 0);
lean_inc(x_120);
lean_dec(x_112);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_122 = !lean_is_exclusive(x_40);
if (x_122 == 0)
{
return x_40;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_40, 0);
lean_inc(x_123);
lean_dec(x_40);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_35, 0);
lean_inc(x_125);
lean_dec(x_35);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
else
{
lean_object* x_129; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_129 = l_Lean_Meta_getNatValue_x3f(x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
lean_inc_ref(x_1);
x_132 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_131);
lean_inc_ref(x_1);
x_135 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = lean_unbox(x_136);
lean_dec(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_139 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 1, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_137);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_141 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_144 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_142);
x_145 = l_Lean_mkApp3(x_143, x_26, x_23, x_144);
x_146 = lean_unsigned_to_nat(0u);
x_147 = l_Lean_Meta_Grind_pushNewFact(x_145, x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_148 = lean_ctor_get(x_141, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_151 = lean_ctor_get(x_135, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_152 = x_135;
} else {
 lean_dec_ref(x_135);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
else
{
lean_object* x_154; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_26);
x_154 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_23);
x_158 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_160);
x_164 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_160, x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = l_Int_Linear_Expr_norm(x_165);
x_167 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_168 = l_Lean_mkApp6(x_167, x_26, x_23, x_156, x_160, x_157, x_161);
lean_inc(x_131);
x_169 = lean_nat_to_int(x_131);
x_170 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_170, 0, x_1);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_170, 2, x_131);
lean_ctor_set(x_170, 3, x_165);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_166);
lean_ctor_set(x_171, 2, x_170);
x_172 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_131);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_173 = lean_ctor_get(x_164, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_174 = x_164;
} else {
 lean_dec_ref(x_164);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_131);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_176 = lean_ctor_get(x_162, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_177 = x_162;
} else {
 lean_dec_ref(x_162);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_131);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_179 = lean_ctor_get(x_158, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_180 = x_158;
} else {
 lean_dec_ref(x_158);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_131);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_182 = lean_ctor_get(x_154, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_183 = x_154;
} else {
 lean_dec_ref(x_154);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_131);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_185 = lean_ctor_get(x_132, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_186 = x_132;
} else {
 lean_dec_ref(x_132);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_130);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_2);
x_188 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
x_190 = lean_ctor_get_uint8(x_189, sizeof(void*)*11 + 14);
lean_dec(x_189);
if (x_190 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_192 = l_Lean_indentExpr(x_1);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Meta_Grind_reportIssue(x_193, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_194) == 0)
{
lean_dec_ref(x_194);
x_17 = lean_box(0);
goto block_20;
}
else
{
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_188, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_198 = lean_ctor_get(x_129, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_199 = x_129;
} else {
 lean_dec_ref(x_129);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
}
}
}
else
{
uint8_t x_201; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
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
x_201 = !lean_is_exclusive(x_35);
if (x_201 == 0)
{
return x_35;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_35, 0);
lean_inc(x_202);
lean_dec(x_35);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
}
}
}
}
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
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 22);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
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
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
lean_inc_ref(x_1);
x_18 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_24 = l_Lean_Expr_cleanupAnnotations(x_19);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
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
goto block_23;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
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
goto block_23;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
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
goto block_23;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
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
goto block_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_dec_ref(x_32);
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
goto block_23;
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_20);
x_36 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
x_37 = l_Lean_Expr_isConstOf(x_32, x_36);
lean_dec_ref(x_32);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_39;
}
}
}
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_40; 
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
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_13, 0);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*11 + 22);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
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
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc_ref(x_1);
x_47 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_53 = l_Lean_Expr_cleanupAnnotations(x_48);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec_ref(x_53);
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
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_dec_ref(x_55);
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
goto block_52;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec_ref(x_57);
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
goto block_52;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_60 = l_Lean_Expr_isApp(x_59);
if (x_60 == 0)
{
lean_dec_ref(x_59);
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
goto block_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_61);
x_62 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_63 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
x_64 = l_Lean_Expr_isConstOf(x_62, x_63);
lean_dec_ref(x_62);
if (x_64 == 0)
{
lean_dec_ref(x_61);
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
goto block_52;
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_49);
x_65 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
x_66 = l_Lean_Expr_isConstOf(x_61, x_65);
lean_dec_ref(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_68;
}
}
}
}
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
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
x_69 = lean_ctor_get(x_47, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_70 = x_47;
} else {
 lean_dec_ref(x_47);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
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
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
return x_13;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
lean_dec(x_13);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
