// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Proof
// Imports: public import Lean.Meta.Tactic.Grind.Order.OrderM public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Init.Grind.Order
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
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "le_trans"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 43, 191, 112, 137, 193, 135, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_lt_trans"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value),LEAN_SCALAR_PTR_LITERAL(86, 5, 164, 57, 63, 70, 156, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lt_le_trans"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 146, 133, 68, 19, 79, 184, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lt_trans"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 60, 83, 238, 3, 34, 17, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(lean_object**);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_trans_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(126, 251, 181, 144, 176, 206, 66, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "le_lt_trans_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value),LEAN_SCALAR_PTR_LITERAL(31, 101, 95, 20, 187, 58, 61, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lt_le_trans_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value),LEAN_SCALAR_PTR_LITERAL(225, 26, 24, 221, 100, 92, 208, 48)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lt_trans_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(95, 242, 92, 104, 20, 156, 104, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Tactic.Grind.Order.Proof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "_private.Lean.Meta.Tactic.Grind.Order.Proof.0.Lean.Meta.Grind.Order.mkPropagateEqTrueProofCore"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: k.strict && !k'.strict\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "le_eq_true_of_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(63, 249, 195, 71, 0, 205, 249, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value;
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "le_eq_true_of_le_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 120, 231, 254, 238, 65, 56, 52)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "le_eq_true_of_lt_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 107, 227, 129, 18, 225, 202, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lt_eq_true_of_le_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 249, 82, 202, 166, 216, 45, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lt_eq_true_of_lt_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 121, 190, 17, 214, 174, 179, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_eq_true_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 108, 221, 174, 248, 219, 86, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lt_eq_true_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 176, 103, 137, 209, 152, 134, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 69, 58, 88, 27, 98, 61, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Meta.Grind.Order.mkPropagateSelfEqTrueProof"};
static const lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: !k.strict\n    "};
static const lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "_private.Lean.Meta.Tactic.Grind.Order.Proof.0.Lean.Meta.Grind.Order.mkPropagateEqFalseProofCore"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "le_eq_false_of_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 209, 34, 178, 202, 43, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lt_eq_false_of_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(109, 127, 250, 67, 115, 231, 55, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lt_eq_false_of_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(92, 54, 53, 77, 81, 230, 245, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "le_eq_false_of_le_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 209, 42, 184, 86, 97, 154, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "le_eq_false_of_lt_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 163, 205, 73, 71, 111, 202, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lt_eq_false_of_le_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value),LEAN_SCALAR_PTR_LITERAL(10, 192, 79, 69, 10, 187, 56, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lt_eq_false_of_lt_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value),LEAN_SCALAR_PTR_LITERAL(249, 203, 190, 147, 19, 93, 170, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "le_eq_false_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 240, 113, 117, 112, 170, 151, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lt_eq_false_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(208, 106, 237, 135, 74, 208, 230, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lt_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 58, 205, 17, 146, 41, 125, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Meta.Grind.Order.mkPropagateSelfEqFalseProof"};
static const lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: k.strict\n    "};
static const lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lt_unsat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 234, 248, 132, 18, 253, 75, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_unsat_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 202, 95, 222, 63, 197, 196, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lt_unsat_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 211, 45, 13, 71, 40, 56, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Meta.Tactic.Grind.Order.Proof.0.Lean.Meta.Grind.Order.mkUnsatProofCore"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 46, .m_data = "assertion violation: k₁.strict || k₂.strict\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_of_le_of_le"};
static const lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 212, 9, 85, 237, 19, 58, 63)}};
static const lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "eq_of_le_of_le_0"};
static const lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 244, 161, 56, 90, 231, 118, 34)}};
static const lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_1, x_22);
x_24 = l_Lean_mkApp3(x_23, x_17, x_20, x_19);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_mkConst(x_1, x_31);
x_33 = l_Lean_mkApp3(x_32, x_26, x_29, x_28);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 6);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_1, x_22);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_29 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_28);
x_24 = x_29;
goto block_27;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec_ref(x_20);
x_24 = x_30;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkApp3(x_23, x_17, x_19, x_24);
if (lean_is_scalar(x_16)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_16;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 8);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_mkConst(x_1, x_23);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_36 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_35);
x_30 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
lean_dec_ref(x_20);
x_30 = x_37;
goto block_34;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_mkApp4(x_24, x_17, x_19, x_25, x_26);
if (lean_is_scalar(x_16)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_16;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
block_34:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_32 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_31);
x_25 = x_30;
x_26 = x_32;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec_ref(x_21);
x_25 = x_30;
x_26 = x_33;
goto block_29;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_19);
lean_dec(x_15);
x_20 = l_Lean_Expr_app___override(x_18, x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_app___override(x_21, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_23 = lean_ctor_get(x_15, 7);
lean_inc(x_23);
lean_dec(x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_25 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_24);
x_19 = x_25;
goto block_22;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec_ref(x_23);
x_19 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Expr_app___override(x_17, x_19);
if (lean_is_scalar(x_18)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_18;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 7);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_1, x_22);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_29 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_28);
x_24 = x_29;
goto block_27;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec_ref(x_20);
x_24 = x_30;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkApp3(x_23, x_17, x_19, x_24);
if (lean_is_scalar(x_16)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_16;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_24 = lean_ctor_get(x_15, 10);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 11);
lean_inc(x_25);
lean_dec(x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_32 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_31);
x_26 = x_32;
goto block_30;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec_ref(x_24);
x_26 = x_33;
goto block_30;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_mkAppB(x_17, x_19, x_20);
if (lean_is_scalar(x_18)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_18;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
block_30:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_28 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_27);
x_19 = x_26;
x_20 = x_28;
goto block_23;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
x_19 = x_26;
x_20 = x_29;
goto block_23;
}
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_24 = lean_ctor_get(x_15, 10);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 11);
lean_inc(x_25);
lean_dec(x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_32 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_31);
x_26 = x_32;
goto block_30;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec_ref(x_24);
x_26 = x_33;
goto block_30;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_mkAppB(x_17, x_19, x_20);
if (lean_is_scalar(x_18)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_18;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
block_30:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_28 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_27);
x_19 = x_26;
x_20 = x_28;
goto block_23;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
x_19 = x_26;
x_20 = x_29;
goto block_23;
}
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; lean_object* x_21; 
if (x_4 == 0)
{
if (x_5 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4));
x_26 = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_20 = x_27;
x_21 = lean_box(0);
goto block_24;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6));
x_29 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_20 = x_30;
x_21 = lean_box(0);
goto block_24;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_29;
}
}
}
else
{
if (x_5 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8));
x_32 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_20 = x_33;
x_21 = lean_box(0);
goto block_24;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_32;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10));
x_35 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_20 = x_36;
x_21 = lean_box(0);
goto block_24;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_mkApp5(x_20, x_1, x_2, x_3, x_6, x_7);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_4);
x_21 = lean_unbox(x_5);
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(x_1, x_2, x_3, x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_19 = x_1;
} else {
 lean_dec_ref(x_1);
 x_19 = lean_box(0);
}
x_28 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec_ref(x_17);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_2);
x_32 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec_ref(x_28);
x_33 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_53; uint8_t x_58; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_45 = lean_ctor_get(x_34, 14);
lean_inc_ref(x_45);
lean_dec(x_34);
x_46 = l_Lean_instInhabitedExpr;
x_58 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_45, x_16);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_outOfBounds___redArg(x_46);
x_53 = x_59;
goto block_57;
}
else
{
lean_object* x_60; 
lean_inc_ref(x_45);
x_60 = l_Lean_PersistentArray_get_x21___redArg(x_46, x_45, x_16);
x_53 = x_60;
goto block_57;
}
block_44:
{
lean_object* x_38; 
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(x_36, x_35, x_37, x_29, x_32, x_18, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
if (x_29 == 0)
{
x_20 = x_39;
x_21 = lean_box(0);
x_22 = x_40;
x_23 = x_32;
goto block_27;
}
else
{
x_20 = x_39;
x_21 = lean_box(0);
x_22 = x_40;
x_23 = x_29;
goto block_27;
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec(x_16);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
block_52:
{
uint8_t x_49; 
x_49 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_45, x_3);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_45);
x_50 = l_outOfBounds___redArg(x_46);
x_35 = x_48;
x_36 = x_47;
x_37 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_PersistentArray_get_x21___redArg(x_46, x_45, x_3);
x_35 = x_48;
x_36 = x_47;
x_37 = x_51;
goto block_44;
}
}
block_57:
{
uint8_t x_54; 
x_54 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_45, x_30);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_30);
x_55 = l_outOfBounds___redArg(x_46);
x_47 = x_53;
x_48 = x_55;
goto block_52;
}
else
{
lean_object* x_56; 
lean_inc_ref(x_45);
x_56 = l_Lean_PersistentArray_get_x21___redArg(x_46, x_45, x_30);
lean_dec(x_30);
x_47 = x_53;
x_48 = x_56;
goto block_52;
}
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_16);
x_61 = !lean_is_exclusive(x_33);
if (x_61 == 0)
{
return x_33;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_33, 0);
lean_inc(x_62);
lean_dec(x_33);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_19)) {
 x_25 = lean_alloc_ctor(0, 3, 0);
} else {
 x_25 = x_19;
}
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_20);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_65 == 0)
{
uint8_t x_82; 
x_82 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13));
x_84 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_83, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_66 = x_85;
x_67 = lean_box(0);
goto block_81;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_84;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15));
x_87 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_86, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_66 = x_88;
x_67 = lean_box(0);
goto block_81;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_87;
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17));
x_91 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_90, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_66 = x_92;
x_67 = lean_box(0);
goto block_81;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_91;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19));
x_94 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_93, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_66 = x_95;
x_67 = lean_box(0);
goto block_81;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_94;
}
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_mkApp6(x_21, x_1, x_2, x_3, x_22, x_23, x_24);
x_26 = l_Lean_eagerReflBoolTrue;
x_27 = l_Lean_mkApp3(x_25, x_6, x_7, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
block_46:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_36 = lean_int_dec_le(x_35, x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_38 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_39 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_40 = lean_int_neg(x_32);
lean_dec(x_32);
x_41 = l_Int_toNat(x_40);
lean_dec(x_40);
x_42 = l_Lean_instToExprInt_mkNat(x_41);
x_43 = l_Lean_mkApp3(x_37, x_38, x_39, x_42);
x_20 = lean_box(0);
x_21 = x_31;
x_22 = x_33;
x_23 = x_34;
x_24 = x_43;
goto block_29;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Int_toNat(x_32);
lean_dec(x_32);
x_45 = l_Lean_instToExprInt_mkNat(x_44);
x_20 = lean_box(0);
x_21 = x_31;
x_22 = x_33;
x_23 = x_34;
x_24 = x_45;
goto block_29;
}
}
block_63:
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_53 = lean_int_dec_le(x_52, x_48);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_55 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_56 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_57 = lean_int_neg(x_48);
x_58 = l_Int_toNat(x_57);
lean_dec(x_57);
x_59 = l_Lean_instToExprInt_mkNat(x_58);
x_60 = l_Lean_mkApp3(x_54, x_55, x_56, x_59);
x_30 = lean_box(0);
x_31 = x_49;
x_32 = x_50;
x_33 = x_51;
x_34 = x_60;
goto block_46;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Int_toNat(x_48);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_30 = lean_box(0);
x_31 = x_49;
x_32 = x_50;
x_33 = x_51;
x_34 = x_62;
goto block_46;
}
}
block_81:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = lean_int_add(x_64, x_68);
x_70 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_71 = lean_int_dec_le(x_70, x_64);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_73 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_74 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_75 = lean_int_neg(x_64);
x_76 = l_Int_toNat(x_75);
lean_dec(x_75);
x_77 = l_Lean_instToExprInt_mkNat(x_76);
x_78 = l_Lean_mkApp3(x_72, x_73, x_74, x_77);
x_47 = lean_box(0);
x_48 = x_68;
x_49 = x_66;
x_50 = x_69;
x_51 = x_78;
goto block_63;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Int_toNat(x_64);
x_80 = l_Lean_instToExprInt_mkNat(x_79);
x_47 = lean_box(0);
x_48 = x_68;
x_49 = x_66;
x_50 = x_69;
x_51 = x_80;
goto block_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_19 = x_1;
} else {
 lean_dec_ref(x_1);
 x_19 = lean_box(0);
}
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_30);
lean_dec_ref(x_2);
x_31 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_55; uint8_t x_60; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_47 = lean_ctor_get(x_32, 14);
lean_inc_ref(x_47);
lean_dec(x_32);
x_48 = l_Lean_instInhabitedExpr;
x_60 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_47, x_16);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_outOfBounds___redArg(x_48);
x_55 = x_61;
goto block_59;
}
else
{
lean_object* x_62; 
lean_inc_ref(x_47);
x_62 = l_Lean_PersistentArray_get_x21___redArg(x_48, x_47, x_16);
x_55 = x_62;
goto block_59;
}
block_46:
{
lean_object* x_36; 
x_36 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(x_34, x_33, x_35, x_17, x_29, x_18, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec_ref(x_17);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec_ref(x_29);
x_42 = lean_int_add(x_38, x_40);
lean_dec(x_40);
lean_dec(x_38);
if (x_39 == 0)
{
x_20 = lean_box(0);
x_21 = x_37;
x_22 = x_42;
x_23 = x_41;
goto block_27;
}
else
{
x_20 = lean_box(0);
x_21 = x_37;
x_22 = x_42;
x_23 = x_39;
goto block_27;
}
}
else
{
uint8_t x_43; 
lean_dec_ref(x_29);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_16);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
block_54:
{
uint8_t x_51; 
x_51 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_47, x_3);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_47);
x_52 = l_outOfBounds___redArg(x_48);
x_33 = x_50;
x_34 = x_49;
x_35 = x_52;
goto block_46;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_PersistentArray_get_x21___redArg(x_48, x_47, x_3);
x_33 = x_50;
x_34 = x_49;
x_35 = x_53;
goto block_46;
}
}
block_59:
{
uint8_t x_56; 
x_56 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(x_47, x_28);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_28);
x_57 = l_outOfBounds___redArg(x_48);
x_49 = x_55;
x_50 = x_57;
goto block_54;
}
else
{
lean_object* x_58; 
lean_inc_ref(x_47);
x_58 = l_Lean_PersistentArray_get_x21___redArg(x_48, x_47, x_28);
lean_dec(x_28);
x_49 = x_55;
x_50 = x_58;
goto block_54;
}
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
x_63 = !lean_is_exclusive(x_31);
if (x_63 == 0)
{
return x_31;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_31, 0);
lean_inc(x_64);
lean_dec(x_31);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_19)) {
 x_25 = lean_alloc_ctor(0, 3, 0);
} else {
 x_25 = x_19;
}
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Order_isRing(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Order_mkTrans(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0);
x_15 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_panic_fn(x_15, x_1);
x_17 = lean_apply_12(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(133u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_21; uint8_t x_22; 
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_21 == 0)
{
if (x_22 == 0)
{
lean_object* x_32; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = l_Lean_Meta_mkEqTrue(x_4, x_13, x_14, x_15, x_16);
return x_32;
}
else
{
goto block_31;
}
}
else
{
if (x_22 == 0)
{
goto block_31;
}
else
{
lean_object* x_33; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = l_Lean_Meta_mkEqTrue(x_4, x_13, x_14, x_15, x_16);
return x_33;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3);
x_19 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
block_31:
{
if (x_21 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_20;
}
else
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5));
x_24 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_mkApp3(x_26, x_1, x_2, x_4);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_mkApp3(x_28, x_1, x_2, x_4);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_43; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_27 == 0)
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1));
x_43 = x_60;
goto block_58;
}
else
{
lean_object* x_61; 
x_61 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3));
x_43 = x_61;
goto block_58;
}
}
else
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5));
x_43 = x_63;
goto block_58;
}
else
{
lean_object* x_64; 
x_64 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7));
x_43 = x_64;
goto block_58;
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_eagerReflBoolTrue;
x_23 = l_Lean_mkApp6(x_19, x_1, x_2, x_20, x_21, x_22, x_4);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
block_42:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_32 = lean_int_dec_le(x_31, x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_34 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_35 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_36 = lean_int_neg(x_26);
x_37 = l_Int_toNat(x_36);
lean_dec(x_36);
x_38 = l_Lean_instToExprInt_mkNat(x_37);
x_39 = l_Lean_mkApp3(x_33, x_34, x_35, x_38);
x_18 = lean_box(0);
x_19 = x_29;
x_20 = x_30;
x_21 = x_39;
goto block_25;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Int_toNat(x_26);
x_41 = l_Lean_instToExprInt_mkNat(x_40);
x_18 = lean_box(0);
x_19 = x_29;
x_20 = x_30;
x_21 = x_41;
goto block_25;
}
}
block_58:
{
lean_object* x_44; 
x_44 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_48 = lean_int_dec_le(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_50 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_51 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_52 = lean_int_neg(x_46);
x_53 = l_Int_toNat(x_52);
lean_dec(x_52);
x_54 = l_Lean_instToExprInt_mkNat(x_53);
x_55 = l_Lean_mkApp3(x_49, x_50, x_51, x_54);
x_28 = lean_box(0);
x_29 = x_45;
x_30 = x_55;
goto block_42;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Int_toNat(x_46);
x_57 = l_Lean_instToExprInt_mkNat(x_56);
x_28 = lean_box(0);
x_29 = x_45;
x_30 = x_57;
goto block_42;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Order_isRing(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_23 == 0)
{
lean_object* x_39; 
x_39 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1));
x_24 = x_39;
goto block_38;
}
else
{
lean_object* x_40; 
x_40 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3));
x_24 = x_40;
goto block_38;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_eagerReflBoolTrue;
x_19 = l_Lean_mkApp3(x_15, x_1, x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
block_38:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_28 = lean_int_dec_le(x_27, x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_30 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_32 = lean_int_neg(x_22);
x_33 = l_Int_toNat(x_32);
lean_dec(x_32);
x_34 = l_Lean_instToExprInt_mkNat(x_33);
x_35 = l_Lean_mkApp3(x_29, x_30, x_31, x_34);
x_15 = x_26;
x_16 = lean_box(0);
x_17 = x_35;
goto block_21;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Int_toNat(x_22);
x_37 = l_Lean_instToExprInt_mkNat(x_36);
x_15 = x_26;
x_16 = lean_box(0);
x_17 = x_37;
goto block_21;
}
}
else
{
lean_dec_ref(x_1);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1));
x_15 = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Expr_app___override(x_17, x_1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_Expr_app___override(x_19, x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_dec_ref(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(175u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_isRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_20 = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2);
x_21 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
return x_22;
}
}
else
{
uint8_t x_23; 
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
lean_dec(x_3);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1));
x_2 = lean_unsigned_to_nat(22u);
x_3 = lean_unsigned_to_nat(183u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2);
x_30 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(x_29);
x_18 = x_30;
goto block_26;
}
else
{
lean_object* x_31; 
x_31 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4));
x_18 = x_31;
goto block_26;
}
}
else
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6));
x_18 = x_33;
goto block_26;
}
else
{
lean_object* x_34; 
x_34 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8));
x_18 = x_34;
goto block_26;
}
}
block_26:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_mkApp3(x_21, x_1, x_2, x_4);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_mkApp3(x_23, x_1, x_2, x_4);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_43; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_27 == 0)
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1));
x_43 = x_60;
goto block_58;
}
else
{
lean_object* x_61; 
x_61 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3));
x_43 = x_61;
goto block_58;
}
}
else
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5));
x_43 = x_63;
goto block_58;
}
else
{
lean_object* x_64; 
x_64 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7));
x_43 = x_64;
goto block_58;
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_eagerReflBoolTrue;
x_23 = l_Lean_mkApp6(x_18, x_1, x_2, x_20, x_21, x_22, x_4);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
block_42:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_32 = lean_int_dec_le(x_31, x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_34 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_35 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_36 = lean_int_neg(x_26);
x_37 = l_Int_toNat(x_36);
lean_dec(x_36);
x_38 = l_Lean_instToExprInt_mkNat(x_37);
x_39 = l_Lean_mkApp3(x_33, x_34, x_35, x_38);
x_18 = x_28;
x_19 = lean_box(0);
x_20 = x_30;
x_21 = x_39;
goto block_25;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Int_toNat(x_26);
x_41 = l_Lean_instToExprInt_mkNat(x_40);
x_18 = x_28;
x_19 = lean_box(0);
x_20 = x_30;
x_21 = x_41;
goto block_25;
}
}
block_58:
{
lean_object* x_44; 
x_44 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_48 = lean_int_dec_le(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_50 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_51 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_52 = lean_int_neg(x_46);
x_53 = l_Int_toNat(x_52);
lean_dec(x_52);
x_54 = l_Lean_instToExprInt_mkNat(x_53);
x_55 = l_Lean_mkApp3(x_49, x_50, x_51, x_54);
x_28 = x_45;
x_29 = lean_box(0);
x_30 = x_55;
goto block_42;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Int_toNat(x_46);
x_57 = l_Lean_instToExprInt_mkNat(x_56);
x_28 = x_45;
x_29 = lean_box(0);
x_30 = x_57;
goto block_42;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Order_isRing(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_23 == 0)
{
lean_object* x_39; 
x_39 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1));
x_24 = x_39;
goto block_38;
}
else
{
lean_object* x_40; 
x_40 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3));
x_24 = x_40;
goto block_38;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_eagerReflBoolTrue;
x_19 = l_Lean_mkApp3(x_15, x_1, x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
block_38:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_28 = lean_int_dec_le(x_27, x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_30 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_32 = lean_int_neg(x_22);
x_33 = l_Int_toNat(x_32);
lean_dec(x_32);
x_34 = l_Lean_instToExprInt_mkNat(x_33);
x_35 = l_Lean_mkApp3(x_29, x_30, x_31, x_34);
x_15 = x_26;
x_16 = lean_box(0);
x_17 = x_35;
goto block_21;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Int_toNat(x_22);
x_37 = l_Lean_instToExprInt_mkNat(x_36);
x_15 = x_26;
x_16 = lean_box(0);
x_17 = x_37;
goto block_21;
}
}
else
{
lean_dec_ref(x_1);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1));
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Expr_app___override(x_17, x_1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_Expr_app___override(x_19, x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_dec_ref(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(228u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_isRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_1);
x_19 = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2);
x_20 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
return x_22;
}
}
else
{
uint8_t x_23; 
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
lean_dec(x_3);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_mkAppB(x_18, x_1, x_2);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_mkAppB(x_20, x_1, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_24 == 0)
{
lean_object* x_40; 
x_40 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
x_25 = x_40;
goto block_39;
}
else
{
lean_object* x_41; 
x_41 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
x_25 = x_41;
goto block_39;
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_eagerReflBoolTrue;
x_20 = l_Lean_mkApp4(x_17, x_1, x_18, x_19, x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
block_39:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_29 = lean_int_dec_le(x_28, x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_32 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_33 = lean_int_neg(x_23);
x_34 = l_Int_toNat(x_33);
lean_dec(x_33);
x_35 = l_Lean_instToExprInt_mkNat(x_34);
x_36 = l_Lean_mkApp3(x_30, x_31, x_32, x_35);
x_16 = lean_box(0);
x_17 = x_27;
x_18 = x_36;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Int_toNat(x_23);
x_38 = l_Lean_instToExprInt_mkNat(x_37);
x_16 = lean_box(0);
x_17 = x_27;
x_18 = x_38;
goto block_22;
}
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_4);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Order_isRing(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_4);
lean_dec_ref(x_2);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(255u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_inc_ref_n(x_1, 2);
x_21 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(x_1, x_2, x_1, x_19, x_20, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (x_19 == 0)
{
if (x_20 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
lean_dec_ref(x_1);
x_32 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2);
x_33 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_33;
}
else
{
goto block_31;
}
}
else
{
goto block_31;
}
block_31:
{
lean_object* x_23; lean_object* x_24; 
x_23 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
x_24 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_mkAppB(x_26, x_1, x_22);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_mkAppB(x_28, x_1, x_22);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_1);
return x_24;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
lean_inc_ref_n(x_1, 2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(x_1, x_2, x_1, x_3, x_5, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_30 == 0)
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
x_31 = x_51;
goto block_47;
}
else
{
goto block_49;
}
}
else
{
goto block_49;
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_eagerReflBoolTrue;
x_26 = l_Lean_mkApp4(x_22, x_1, x_24, x_25, x_20);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_47:
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_int_add(x_29, x_34);
x_36 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
x_37 = lean_int_dec_le(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
x_39 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
x_40 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
x_41 = lean_int_neg(x_35);
lean_dec(x_35);
x_42 = l_Int_toNat(x_41);
lean_dec(x_41);
x_43 = l_Lean_instToExprInt_mkNat(x_42);
x_44 = l_Lean_mkApp3(x_38, x_39, x_40, x_43);
x_22 = x_33;
x_23 = lean_box(0);
x_24 = x_44;
goto block_28;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Int_toNat(x_35);
lean_dec(x_35);
x_46 = l_Lean_instToExprInt_mkNat(x_45);
x_22 = x_33;
x_23 = lean_box(0);
x_24 = x_46;
goto block_28;
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_1);
return x_32;
}
}
block_49:
{
lean_object* x_48; 
x_48 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
x_31 = x_48;
goto block_47;
}
}
else
{
lean_dec_ref(x_1);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Grind_Order_isRing(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Grind_Order_mkUnsatProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1));
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_mkApp4(x_20, x_1, x_2, x_3, x_4);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_mkApp4(x_22, x_1, x_2, x_3, x_4);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1));
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Grind_Order_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_28 = lean_ctor_get(x_21, 10);
lean_inc(x_28);
lean_dec(x_21);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
x_30 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(x_29);
x_23 = x_30;
goto block_27;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_23 = x_31;
goto block_27;
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Expr_app___override(x_19, x_23);
x_25 = l_Lean_mkApp4(x_24, x_1, x_2, x_3, x_4);
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_isRing(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_5);
return x_17;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Init_Grind_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
